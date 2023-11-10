
Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (t : trace) (m : mem) (l : locals).

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : String.string) (post : word -> Prop) : Prop :=
    exists v, map.get l x = Some v /\ post v.
  Definition load s m a (post : word -> Prop) : Prop :=
    exists v, load s m a = Some v /\ post v.
  Definition store sz m a v (post : mem -> Prop) : Prop :=
    exists m', store sz m a v = Some m' /\ post m'.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    (* conceptually, maybe it doesn't make a great deal of sense to pass in the trace, and we
       should just rewrite this function so that it's like we're always passing in a trace of nil.
       it's easier to work with this way, though. *)
    Definition expr_body rec (t : trace) (e : Syntax.expr) (post : trace -> word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v (post t)
      | expr.var x =>
        get l x (post t)
      | expr.op op e1 e2 =>
        rec t e1 (fun t' v1 =>
        rec t' e2 (fun t'' v2 =>
        post t'' (interp_binop op v1 v2)))
      | expr.load s e =>
        rec t e (fun t' a =>
        load s m a (post (cons (read s a) t')))
      | expr.inlinetable s tbl e =>
        rec t e (fun t' a =>
        load s (map.of_list_word tbl) a (post t'))
      | expr.ite c e1 e2 =>
        rec t c (fun t' b =>
        rec (cons (if word.eqb b (word.of_Z 0) then branch false else branch true) t') (if word.eqb b (word.of_Z 0) then e2 else e1) (fun t'' v =>
        post t'' v))
    end.
    Fixpoint expr t e := expr_body expr t e.
  End WithMemAndLocals.

   Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
   End WithF.

   Section WithF'.
    Context {A B T} (f: T -> A -> (T -> B -> Prop) -> Prop).
    Definition list_map'_body rec (acc : T) (xs : list A) (post : T -> list B -> Prop) : Prop :=
      match xs with
      | nil => post acc nil
      | cons x xs' =>
        f acc x (fun acc' y =>
        rec acc' xs' (fun acc'' ys' =>
        post acc'' (cons y ys')))
      end.
    Fixpoint list_map' acc xs := list_map'_body list_map' acc xs.
   End WithF'.

  (*Section WithF2.
    Context {A B C} (f: C -> A -> (C -> B -> Prop) -> Prop).
    Definition list_map2_body rec (xs : list A) (acc : C) (post : list B -> C -> Prop) : Prop :=
      match xs with
      | nil => post nil acc 
      | cons x xs' =>
        f acc x (fun y z =>
        rec xs' z (fun ys' z' =>
        post (cons y ys') z'))
      end.
    Fixpoint list_map2 xs := list_map2_body list_map2 xs.
  End WithF2.*)
  
  Section WithFunctions.
    Context (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Definition dexpr m l t e v t' := expr m l t e (fun t'2 v2 => eq t' t'2 /\ eq v v2).
    Definition dexprs m l t es vs t' := list_map' (expr m l) t es (fun t'2 vs2 => eq t' t'2 /\ eq vs vs2).
    Goal (forall m l t, dexprs m l t (cons (expr.load access_size.one (expr.literal 5)) nil) = dexprs m l t nil). cbv [dexprs]. simpl. Abort.
    Definition cmd_body (rec:_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        exists v t', dexpr m l t ev v t' /\
        dlet! l := map.put l x v in
        post t' m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l
      | cmd.store sz ea ev =>
        exists a t', dexpr m l t ea a t' /\
        exists v t'', dexpr m l t' ev v t'' /\
        store sz m a v (fun m =>
        post (cons (write sz a) t'') m l)
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c (cons (salloc a) t) mCombined l (fun t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l')
      | cmd.cond br ct cf =>
        exists v t', dexpr m l t br v t' /\
        (word.unsigned v <> 0%Z -> rec ct (cons (branch true) t') m l post) /\
        (word.unsigned v = 0%Z -> rec cf (cons (branch false) t') m l post)
      | cmd.seq c1 c2 =>
        rec c1 t m l (fun t m l => rec c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          exists b t', dexpr m l t e b t' /\
          (word.unsigned b <> 0%Z -> rec c (cons (branch true) t') m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
            (word.unsigned b = 0%Z -> post (cons (branch false) t') m l))
      | cmd.call binds fname arges =>
        exists args t', dexprs m l t arges args t' /\ (* (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop) *)
        call fname t' m args (fun t'' m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t'' m l')
      | cmd.interact binds action arges =>
        exists args t', dexprs m l t arges args t' /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec (filterio t') mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons (IO ((mGive, action, args), (mReceive, rets))) t') m' l')
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : trace) (m : mem) (args : list word) (post : trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (t : trace) (m : mem) (args : list word)
                (post : trace -> mem -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl t m args post
      else rec functions fname t m args post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l post : Prop := cmd (call funcs) main t m l post.
End WeakestPrecondition.
Check @cmd_body.
Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec CA
                      (@cmd width BW word mem locals ext_spec CA) c t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.
Check @expr. Check @expr_body.
Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?BW ?word ?mem ?locals ?m ?l ?t ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width BW word mem locals m l (@expr width BW word mem locals m l) t arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.
Check @list_map'. Check @list_map'_body.

Ltac unfold1_list_map' e :=
  lazymatch e with
    @list_map' ?A ?B ?T ?P ?t ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map'_body A B T P (@list_map' A B T P) t arg post)
  end.
Ltac unfold1_list_map'_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map' G in
  change G.
Check @call. Check @call_body.
Ltac unfold1_call e :=
  lazymatch e with
    @call ?width ?BW ?word ?mem ?locals ?ext_spec ?fs ?fname ?t ?m ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body width BW word mem locals ext_spec
                       (@call width BW word mem locals ext_spec) fs fname t m l post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.

Import Coq.ZArith.ZArith.

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
         .. (forall an,
               (forall g0,
                   .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                            rets = (cons r0 .. (cons rn nil) ..) /\
                                              post) ..)))) ..)) ..))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      g0 binder, gn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* general form *)
(* trying out alternate definition with function. *)
Definition appl {A B} (x : A) (f : A -> B) := f x.
Notation "'ctfunc!' name a0 .. an '|' b0 .. bn '/' g0 .. gn '|' h0 .. hn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall b0,
                           .. (forall bn,
                                 (forall g0,
                                     .. (forall gn, 
                                           (forall h0,
                                               .. (forall hn,
                                                     pre ->
                                                     WeakestPrecondition.call
                                                       functions name tr mem (cons a0 .. (cons an (cons b0 .. (cons bn nil) ..)) ..)
                                                       (fun tr' mem' rets =>
                                                          (exists tr'', generates ((appl a0 .. (appl an (appl g0 .. (appl gn f) ..)) ..)) (List.rev tr'') /\
                                                                          tr' = (tr'' ++ tr)%list) /\
                                                            (exists r0,
                                                                .. (exists rn,
                                                                      rets = (cons r0 .. (cons rn nil) ..) /\
                                                                        post) ..))) ..)) ..)) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      b0 binder, bn binder,
      g0 binder, gn binder,
      h0 binder, hn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for swap *)
Notation "'ctfunc!' name a0 .. an '|' '/' '|' h0 .. hn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall h0,
                           .. (forall hn,
                                 pre ->
                                 WeakestPrecondition.call
                                   functions name tr mem (cons a0 .. (cons an nil) ..)
                                   (fun tr' mem' rets =>
                                      (exists tr'',
                                          generates (appl a0 .. (appl an f) ..) (List.rev tr'') /\
                                            tr' = (tr'' ++ tr)%list) /\
                                            rets = nil /\
                                            post)) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      h0 binder, hn binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for memequal *)
Notation "'ctfunc!' name a0 .. an '|' '/' '|' h0 .. hn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall h0,
                           .. (forall hn,
                                 pre ->
                                 WeakestPrecondition.call
                                   functions name tr mem (cons a0 .. (cons an nil) ..)
                                   (fun tr' mem' rets =>
                                      (exists tr'',
                                          generates (appl a0 .. (appl an f) ..) (List.rev tr'') /\
                                            tr' = (tr'' ++ tr)%list) /\
                                        (exists r0,
                                            .. (exists rn,     
                                                  rets = (cons r0 .. (cons rn nil) ..) /\
                                                    post) ..))) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      h0 binder, hn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for stackswap *)
Notation "'ctfunc!' name '|' b0 .. bn '/' '|' '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall b0,
                 .. (forall bn,
                       pre ->
                       WeakestPrecondition.call
                         functions name tr mem (cons b0 .. (cons bn nil) ..)
                         (fun tr' mem' rets =>
                            (exists tr'',
                                generates f (List.rev tr'') /\
                                  tr' = (tr'' ++ tr)%list) /\
                              (exists r0,
                                  .. (exists rn,
                                        rets = (cons r0 .. (cons rn nil) ..) /\
                                          post) ..))) ..))))
    (at level 200,
      name at level 0,
      b0 binder, bn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
         .. (forall an,
               (forall g0,
                   .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      g0 binder, gn binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
         .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                  rets = (cons r0 .. (cons rn nil) ..) /\
                                    post) ..)))) ..))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall an,
         (forall g0,
             .. (forall gn,
                   (forall tr mem,
                       pre ->
                       WeakestPrecondition.call
                         functions name tr mem nil
                         (fun tr' mem' rets =>
                            (exists r0,
                                .. (exists rn,
                                      rets = (cons r0 .. (cons rn nil) ..) /\
                                        post) ..)))) ..)))
    (at level 200,
      name at level 0,
      g0 binder, gn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
         .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        rets = nil /\ post))) ..))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall g0,
         .. (forall gn,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem nil
                     (fun tr' mem' rets =>
                        rets = nil /\ post))) ..))
    (at level 200,
      name at level 0,
      g0 binder, gn binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall tr mem,
         pre ->
         WeakestPrecondition.call
           functions name tr mem nil
           (fun tr' mem' rets =>
              (exists r0,
                  .. (exists rn,
                        rets = (cons r0 .. (cons rn nil) ..) /\
                          post) ..))))
    (at level 200,
      name at level 0,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).
