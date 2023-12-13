
Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (k : trace) (t : io_trace) (m : mem) (l : locals).

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
    Definition expr_body rec (k : trace) (e : Syntax.expr) (post : trace -> word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v (post k)
      | expr.var x =>
        get l x (post k)
      | expr.op op e1 e2 =>
        rec k e1 (fun k' v1 =>
        rec k' e2 (fun k'' v2 =>
        post (app (leak_binop op v1 v2) k'') (interp_binop op v1 v2)))
      | expr.load s e =>
        rec k e (fun k' a =>
        load s m a (post (cons (read a) k')))
      | expr.inlinetable s tbl e =>
        rec k e (fun k' a =>
        load s (map.of_list_word tbl) a (post (cons (table a ) k')))
      | expr.ite c e1 e2 =>
        rec k c (fun k' b =>
        rec (cons (if word.eqb b (word.of_Z 0) then branch false else branch true) k') (if word.eqb b (word.of_Z 0) then e2 else e1) (fun k'' v =>
        post k'' v))
    end.
    Fixpoint expr k e := expr_body expr k e.
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
    Context (call : String.string -> trace -> io_trace -> mem -> list word -> (trace -> io_trace -> mem -> list word -> Prop) -> Prop).
    Definition dexpr m l k e v k' := expr m l k e (fun k'2 v2 => eq k' k'2 /\ eq v v2).
    Definition dexprs m l k es vs k' := list_map' (expr m l) k es (fun k'2 vs2 => eq k' k'2 /\ eq vs vs2).
    Goal (forall m l k, dexprs m l k (cons (expr.load access_size.one (expr.literal 5)) nil) = dexprs m l k nil). cbv [dexprs]. simpl. Abort.
    Definition cmd_body (rec:_->_->_->_->_->(trace->io_trace->_)->Prop) (c : cmd) (k : trace) (t : io_trace) (m : mem) (l : locals)
             (post : trace -> io_trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post k t m l
      | cmd.set x ev =>
        exists v k', dexpr m l k ev v k' /\
        dlet! l := map.put l x v in
        post k' t m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post k t m l
      | cmd.store sz ea ev =>
        exists a k', dexpr m l k ea a k' /\
        exists v k'', dexpr m l k' ev v k'' /\
        store sz m a v (fun m =>
        post (cons (write a) k'') t m l)
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c (cons (salloc a) k) t mCombined l (fun k' t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post k' t' m' l')
      | cmd.cond br ct cf =>
        exists v k', dexpr m l k br v k' /\
        (word.unsigned v <> 0%Z -> rec ct (cons (branch true) k') t m l post) /\
        (word.unsigned v = 0%Z -> rec cf (cons (branch false) k') t m l post)
      | cmd.seq c1 c2 =>
        rec c1 k t m l (fun k t m l => rec c2 k t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->io_trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v k t m l) /\
        (forall v k t m l, inv v k t m l ->
          exists b k', dexpr m l k e b k' /\
          (word.unsigned b <> 0%Z -> rec c (cons (branch true) k') t m l (fun k t m l =>
            exists v', inv v' k t m l /\ lt v' v)) /\
            (word.unsigned b = 0%Z -> post (cons (branch false) k') t m l))
      | cmd.call binds fname arges =>
        exists args k', dexprs m l k arges args k' /\ (* (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop) *)
        call fname k' t m args (fun k'' t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post k'' t m l')
      | cmd.interact binds action arges =>
        exists args k', dexprs m l k arges args k' /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post k' (cons ((mGive, action, args), (mReceive, rets)) t) m' l')
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (k : trace) (t : io_trace) (m : mem) (args : list word) (post : trace -> io_trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c k t m l (fun k t m l =>
        list_map (get l) outnames (fun rets =>
        post k t m rets)). Check func.

  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (k : trace) (t : io_trace) (m : mem) (args : list word)
                (post : trace -> io_trace -> mem -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl k t m args post
      else rec functions fname k t m args post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main k t m l post : Prop := cmd (call funcs) main k t m l post.
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
