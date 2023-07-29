Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Export bedrock2.Memory.

Require Import Coq.Lists.List.

(* BW is not needed on the rhs, but helps infer width *)
Definition iotrace{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  list ((mem * String.string * list word) * (mem * list word)).

(*match t : oldtrace with
  | nil => output_to_explain = None
  | (_, MMInput, [addr], (_, [value]))::trace =>
    if (word.unsigned addr =? uart0_base + 0x004) && (word.unsigned (word.and value (word.of_Z (2 ^ 31))) =? 0)
    then output_to_explain = Some value /\ spec trace None
    else spec trace output_to_explain
  | (_, MMOutput, [addr; value], (_, []))::trace => ( *) Compute (map.map (word.word 1) byte).
Print map.map.

Inductive event{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
| IOevent : mem (* memory state prior to ioevent occurring *) *
              String.string (* type of event, e.g. input or output *) *
              list word (* information about the ioevent that is known before it occurs
                           - for an input event, the address from which the input will be read
                           - for an output event, the address at which the output will be written,
                             as well as the value to be written
                         *) *
              (mem (* memory state after ioevent occurs *) *
                 list word (* information about the ioevent that isn't known until after it occurs
                              - for an input event, the value which was read
                              - for an output event, nothing
                            *)
              ) -> event
| branch : bool -> event
| read : access_size -> word -> event
| write : access_size -> word -> event.

Definition trace{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} := list event.

Definition filterio {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} (t : trace) : iotrace :=
    flat_map (fun e =>
                match e with
                | IOevent e => cons e nil
                | _ => nil
                end) t.

Lemma filterio_cons {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} (t : trace) (e : event) :
  filterio (e :: t) = match e with
                     | IOevent e => cons e nil
                     | _ => nil
                      end ++ filterio t.
Proof. reflexivity. Qed.
                            
Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory and function call results, *)
  (mem -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
          {ext_spec: ExtSpec}: Prop :=
  {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
               (Morphisms.pointwise_relation (list word) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok {_ _ _ _} _.

Section binops.
  Context {width : Z} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End binops.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.

  Local Notation metrics := MetricLog.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern). Print trace. Check expr.inlinetable.
    Print access_size.access_size. Check expr.load.
    Compute (expr.load access_size.one (expr.literal 5)).
    Check expr.inlinetable. Print map.of_list_word.
    Print load.
    (* why does this need mc passed as an argument? can't we union two metrics? so we could just return the change in 
       mc, rather than the total? this style does seem easier to work with. not a big deal anyway. *)
    (* I guess I'll also pass the trace as an argument?  for consistency? *)
    Fixpoint eval_expr (e : expr) (mc : metrics) (tr : trace) : option (word * metrics * trace) :=
      match e with
      | expr.literal v => Some (
                              word.of_Z v,
                              addMetricInstructions 8 (addMetricLoads 8 mc),
                              tr)
      | expr.var x => match map.get l x with
                      | Some v => Some (
                                      v,
                                      addMetricInstructions 1 (addMetricLoads 2 mc),
                                      tr)
                      | None => None
                      end
      (* if i understand correctly, this thing does not access memory at all.
         so no change to leakage trace. *)
      | expr.inlinetable aSize t index =>
          'Some (index', mc', tr') <- eval_expr index mc tr | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (
              v,
              (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc'))),
              tr')
      | expr.load aSize a =>
          'Some (a', mc', tr') <- eval_expr a mc tr | None;
          'Some v <- load aSize m a' | None;
          Some (
              v,
              addMetricInstructions 1 (addMetricLoads 2 mc'),
              read aSize a' :: tr')
      | expr.op op e1 e2 =>
          'Some (v1, mc', tr') <- eval_expr e1 mc tr | None;
          'Some (v2, mc'', tr'') <- eval_expr e2 mc' tr' | None;
          Some (
              interp_binop op v1 v2,
              addMetricInstructions 2 (addMetricLoads 2 mc''),
              tr'')
      | expr.ite c e1 e2 =>
          'Some (vc, mc', tr') <- eval_expr c mc tr | None;
          eval_expr
            (if word.eqb vc (word.of_Z 0) then e2 else e1)
            (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc')))
            tr'
      end.

    Fixpoint eval_expr_old (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.inlinetable aSize t index =>
          'Some index' <- eval_expr_old index | None;
          load aSize (map.of_list_word t) index'
      | expr.load aSize a =>
          'Some a' <- eval_expr_old a | None;
          load aSize m a'
      | expr.op op e1 e2 =>
          'Some v1 <- eval_expr_old e1 | None;
          'Some v2 <- eval_expr_old e2 | None;
          Some (interp_binop op v1 v2)
      | expr.ite c e1 e2 =>
          'Some vc <- eval_expr_old c | None;
          eval_expr_old (if word.eqb vc (word.of_Z 0) then e2 else e1)
    end.

    Fixpoint evaluate_call_args_log (arges : list expr) (mc : metrics) (tr : trace) :=
      match arges with
      | e :: tl =>
        'Some (v, mc', tr') <- eval_expr e mc tr | None;
        'Some (args, mc'', tr'') <- evaluate_call_args_log tl mc' tr' | None;
        Some (v :: args, mc'', tr'')
      | _ => Some (nil, mc, tr)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  Print cmd.cmd. Print trace. Print event. Check cmd.store.
  Compute (cmd.store access_size.one (expr.literal 5) (expr.literal 5)). Print anybytes. Print ftprint.
  Print List.unfoldn. Print map.split. Print ext_spec.
  Inductive exec :
    cmd -> trace -> mem -> locals -> metrics ->
    (trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    t m l mc post
    (_ : post t m l mc)
    : exec cmd.skip t m l mc post
  | set x e
    t m l mc post
    v mc' t' (_ : eval_expr m l e mc t = Some (v, mc', t'))
    (_ : post t' m (map.put l x v) (addMetricInstructions 1
                                  (addMetricLoads 1 mc')))
    : exec (cmd.set x e) t m l mc post
  | unset x
    t m l mc post
    (_ : post t m (map.remove l x) mc)
    : exec (cmd.unset x) t m l mc post
  | store sz ea ev
    t m l mc post
    a mc' t' (_ : eval_expr m l ea mc t = Some (a, mc', t'))
    v mc'' t'' (_ : eval_expr m l ev mc' t' = Some (v, mc'', t''))
    m' (_ : store sz m a v = Some m')
    (_ : post (write sz a :: t'') m' l (addMetricInstructions 1
                                       (addMetricLoads 1
                                          (addMetricStores 1 mc''))))
    : exec (cmd.store sz ea ev) t m l mc post
  | stackalloc x n body
    t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
          (fun t' mCombined' l' mc' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post t' mSmall' l' mc'))
     : exec (cmd.stackalloc x n body) t mSmall l mc post
  | if_true t m l mc e c1 c2 post
    v mc' t' (_ : eval_expr m l e mc t = Some (v, mc', t'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 (branch true :: t') m l (addMetricInstructions 2
                                            (addMetricLoads 2
                                               (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | if_false e c1 c2
    t m l mc post
    v mc' t' (_ : eval_expr m l e mc t = Some (v, mc', t'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 (branch false :: t') m l (addMetricInstructions 2
                                             (addMetricLoads 2
                                                (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | seq c1 c2
    t m l mc post
    mid (_ : exec c1 t m l mc mid)
    (_ : forall t' m' l' mc', mid t' m' l' mc' -> exec c2 t' m' l' mc' post)
    : exec (cmd.seq c1 c2) t m l mc post
  | while_false e c
    t m l mc post
    v mc' t' (_ : eval_expr m l e mc t = Some (v, mc', t'))
    (_ : word.unsigned v = 0)
    (_ : post (branch false :: t') m l (addMetricInstructions 1
                                          (addMetricLoads 1
                                             (addMetricJumps 1 mc'))))
    : exec (cmd.while e c) t m l mc post
  | while_true e c
      t m l mc post
      v mc' t' (_ : eval_expr m l e mc t = Some (v, mc', t'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c (branch true :: t') m l (addMetricInstructions 2
                                                 (addMetricLoads 2
                                                    (addMetricJumps 1 mc'))) mid)
      (_ : forall t'' m' l' mc'', mid t'' m' l' mc'' ->
                                 exec (cmd.while e c) t'' m' l' (*(addMetricInstructions 2
                                                                   (addMetricLoads 2
                                                                      (addMetricJumps 1*) mc''(* )))*) post)
    : exec (cmd.while e c) t m l mc post
  | call binds fname arges
      t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' t' (_ : evaluate_call_args_log m l arges mc t = Some (args, mc', t'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody t' m lf (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc')))) mid)
      (_ : forall t'' m' st1 mc'', mid t'' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t'' m' l'  (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))))
    : exec (cmd.call binds fname arges) t m l mc post
  | interact binds action arges
      t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' t' (_ :  evaluate_call_args_log m l arges mc t = Some (args, mc', t'))
      mid (_ : ext_spec t' mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (IOevent ((mGive, action, args), (mReceive, resvals)) :: t') m' l'
            (addMetricInstructions 1
            (addMetricStores 1
            (addMetricLoads 2 mc'))))
    : exec (cmd.interact binds action arges) t m l mc post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken: forall t l m mc s post1,
      exec s t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> Prop,
        (forall t' m' l' mc', post1 t' m' l' mc' -> post2 t' m' l' mc') ->
        exec s t m l mc post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply stackalloc. 1: assumption.
      intros.
      eapply H1; eauto.
      intros. fwd. eauto 10.
    - eapply call.
      4: eapply IHexec.
      all: eauto.
      intros.
      edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
      eauto 10.
    - eapply interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      eauto 10.
  Qed.

  Lemma intersect: forall t l m mc s post1,
      exec s t m l mc post1 ->
      forall post2,
        exec s t m l mc post2 ->
        exec s t m l mc (fun t' m' l' mc' => post1 t' m' l' mc' /\ post2 t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
             | H1: ?e = Some (?v1, ?mc1, ?t1), H2: ?e = Some (?v2, ?mc2, ?t2) |- _ =>
               replace v2 with v1 in * by congruence;
               replace mc2 with mc1 in * by congruence;
               replace t2 with t1 in * by congruence; clear v2 mc2 t2 H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H12 into Ex2.
      eapply weaken. 1: eapply H1. 1,2: eassumption.
      1: eapply Ex2. 1,2: eassumption.
      cbv beta.
      intros. fwd.
      lazymatch goal with
      | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
        specialize @map.split_diff with (4 := A) (5 := B) as P
      end.
      edestruct P; try typeclasses eauto. 2: subst; eauto 10.
      eapply anybytes_unique_domain; eassumption.
    - econstructor.
      + eapply IHexec. exact H5. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply while_true. 1, 2: eassumption.
      + eapply IHexec. exact H9. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H16. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H17 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.unique_mGive_footprint as P.
      specialize P with (1 := H1) (2 := H14).
      destruct (map.split_diff P H H7). subst mKeep0 mGive0. clear H7.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H14 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H15 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.
End exec. Notation exec := exec.exec.
