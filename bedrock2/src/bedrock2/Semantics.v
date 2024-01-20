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
Definition io_event {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  (mem * String.string * list word) * (mem * list word).

(*could reduce this to many fewer cases, at the cost of being a bit more confusing.*)
(*actually no, it wouldn't even be that confusing.  It's very tempting to just let
event := bool | word | unit. *)
(*should I name this leakage_event, now that it doesn't contain the IO events?*)
Inductive event {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| leak_unit : event
| leak_bool : bool -> event
| leak_word : word -> event
| leak_list : list word -> event
(* ^we need this, because sometimes it's convenient that one io call leaks only one event
   See Interact case of spilling transform_trace function for an example. *)
| consume_word : word -> event.
(*This looks pretty, but it seems hard to work with.  Can't even use the inversion tactic?
Inductive event : Type :=
| leak : forall {A : Type}, A -> event
| consume : forall {A : Type}, A -> event.*)

Inductive qevent {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| qleak_unit : qevent
| qleak_bool : bool -> qevent
| qleak_word : word -> qevent
| qleak_list : list word -> qevent
| qconsume_word : qevent
| qend : qevent.

Inductive abstract_trace {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| empty
| aleak_unit (after : abstract_trace)
| aleak_bool (b : bool) (after : abstract_trace)
| aleak_word (w : word) (after : abstract_trace)
| aleak_list (l : list word) (after : abstract_trace)
| aconsume_word (after : word -> abstract_trace).

Section WithIOEvent.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.
  
  Definition io_trace : Type := list io_event.

  Definition quot e : qevent :=
    match e with
    | leak_unit => qleak_unit
    | leak_bool b => qleak_bool b
    | leak_word w => qleak_word w
    | leak_list l => qleak_list l
    | consume_word w => qconsume_word
    end.

  (*should I call this leakage_trace, now that it doesn't contain io events?
    shame to lengthen the name. No, I shouldn't call it a leakage trace, since 
    it contains the sources of nondeterminism as well as leakage events.*)
  Definition trace : Type := list event.

(* IO things to do:
   set channel: input can either be private or not; output and leak a secret; output and don't leak; output and leak one function of secret,
   take input, output and leak secret but do not leak secret until after input. *)  
  Import ListNotations.
  Inductive generates : abstract_trace -> trace -> Prop :=
  | nil_gen : generates empty nil
  | leak_unit_gen : forall a t_rev,
      generates a t_rev -> generates (aleak_unit a) (leak_unit :: t_rev)
  | leak_bool_gen : forall b a t_rev,
      generates a t_rev -> generates (aleak_bool b a) (leak_bool b :: t_rev)
  | leak_word_gen : forall w a t_rev,
      generates a t_rev -> generates (aleak_word w a) (leak_word w :: t_rev)
  | leak_list_gen : forall l a t_rev,
      generates a t_rev -> generates (aleak_list l a) (leak_list l :: t_rev)
  | consume_word_gen : forall w f t_rev,
      generates (f w) t_rev -> generates (aconsume_word f) (consume_word w :: t_rev).

  Fixpoint abstract_app (a1 a2 : abstract_trace) : abstract_trace :=
    match a1 with
    | empty => a2
    | aleak_unit a1' => aleak_unit (abstract_app a1' a2)
    | aleak_bool b a1' => aleak_bool b (abstract_app a1' a2)
    | aleak_word w a1' => aleak_word w (abstract_app a1' a2)
    | aleak_list l a1' => aleak_list l (abstract_app a1' a2)
    | aconsume_word f => aconsume_word (fun w => abstract_app (f w) a2)
    end.

  Lemma generates_app :
    forall a1 a2 t1 t2,
      generates a1 t1 -> generates a2 t2 -> generates (abstract_app a1 a2) (t1 ++ t2).
  Proof.
    intros a1. induction a1; intros a2 t1 t2 H1 H2; inversion H1; subst; cbn [abstract_app List.app]; try constructor; auto.
  Qed.

  Fixpoint generator (t_rev : trace) : abstract_trace :=
    match t_rev with
    | nil => empty
    | leak_unit :: t_rev' => aleak_unit (generator t_rev')
    | leak_bool b :: t_rev' => aleak_bool b (generator t_rev')
    | leak_word w :: t_rev' => aleak_word w (generator t_rev')
    | leak_list l :: t_rev' => aleak_list l (generator t_rev')
    | consume_word w :: t_rev' => aconsume_word (fun _ => generator t_rev')
    end.

  Lemma generator_generates (t: trace) :
    generates (generator t) t.
  Proof. induction t; try constructor. destruct a; cbn [generator]; constructor; assumption. Qed.

  Section predictors.
    Context {Event QEvent : Type} (qend : QEvent) (q : Event -> QEvent).
    Context (Hend : forall e, q e <> qend).
    Context (Trace := list Event).
    
    Inductive predicts : (Trace -> QEvent) -> Trace -> Prop :=
    | predicts_cons :
      forall f e g t,
        f [] = q e ->
        (forall t', f (e :: t') = g t') ->
        predicts g t ->
        predicts f (e :: t)
    | predicts_nil :
      forall f,
        f [] = qend ->
        predicts f [].


    (*idea: predicts_partly and predictor_valid should take in backwards traces and backward
      predictors, as in 
      Semantics.  Similarly, trace transformation functions should take in backwards *)
    Inductive predicts_partly : (Trace -> QEvent) -> Trace -> Type :=
    | predicts_partly_cons :
      forall f e k,
        f k = q e ->
        predicts_partly f k ->
        predicts_partly f (e :: k)
    | predicts_partly_nil :
      forall f,
        predicts_partly f [].

    (*this takes as input a backwards trace!*)
    (*should I define predicts, predicts_partly like this?
      where the function is fixed, and there's some trace that's changing? *)
    Inductive predictor_valid : Trace -> (Trace -> QEvent) -> Type :=
    | valid_nil :
      forall k f, f k = qend ->
                predictor_valid k f
    | valid_cons :
      forall k f,
        (forall e, q e = f k -> predictor_valid (e :: k) f) ->
        predictor_valid k f.      
    
    Lemma predicts_ext f g t :
      predicts f t ->
      (forall x, f x = g x) ->
      predicts g t.
    Proof.
      intros. generalize dependent g. induction H.
      - econstructor.
        + rewrite <- H. rewrite H2. reflexivity.
        + intros t'. rewrite <- H2. apply H0.
        + eapply IHpredicts. reflexivity.
      - intros. constructor. rewrite <- H0. apply H.
    Qed.

    Lemma predicts_partly_ext f g t :
      (forall t', f t' = g t') ->
      predicts_partly f t ->
      predicts_partly g t.
    Proof.
      intros H1 H2. generalize dependent g. induction H2.
      - intros. apply predicts_partly_cons.
        + rewrite <- H1. assumption.
        + auto.
      - intros. constructor.
    Qed.

    Lemma predictor_valid_ext k f g :
      predictor_valid k f ->
      (forall x, f x = g x) ->
      predictor_valid k g.
    Proof.
      intros H. revert g. induction H; intros g Hfg.
      - apply valid_nil. rewrite <- Hfg. assumption.
      - apply valid_cons. intros. eapply X.
        + rewrite Hfg. apply H.
        + intros. apply Hfg.
    Qed.

    Lemma predicts_partly_app k1 k2 next :
      predicts_partly next k1 ->
      predicts_partly (fun k => next (k ++ k1)) k2 ->
      predicts_partly next (k2 ++ k1).
    Proof.
      revert k1. revert next. induction k2; intros next k1 H1 H2.
      - assumption.
      - inversion H2. subst. constructor; fold (app k2 k1).
        + assumption.
        + apply IHk2; assumption.
    Qed.

    Lemma bigger_thing_valid f k1 k2 :
      predictor_valid k1 f ->
      predicts_partly (fun k => f (k ++ k1)) k2 ->
      predictor_valid (k2 ++ k1) f.
    Proof.
      intros H1. induction k2.
      - intros H2. assumption.
      - intros H2. inversion H2. subst. specialize (IHk2 ltac:(assumption)).
        inversion IHk2; subst.
        + rewrite H3 in H. apply Hend in H. destruct H.
        + apply X0. auto.
    Qed.
    
    Require Import coqutil.Z.Lia.
    
    Definition predict_with_prefix_body (prefix : list Event) (t : list Event)
      (predict_rest : forall (rest : list Event), (length prefix + length rest = length t) -> QEvent)
      (predict_with_prefix : forall (prefix' t' : list Event), (forall rest':list Event, length prefix' + length rest' = length t' -> QEvent) -> QEvent)
      : QEvent.
      refine (
          match prefix as x, t as y return prefix = x -> t = y -> _ with
          | _ :: prefix', _ :: t' => fun _ _ => predict_with_prefix prefix' t' (fun rest pf => predict_rest rest _)
          | e :: start', nil => fun _ _ => q e
          | nil, _ => fun _ _ => predict_rest t _
          end (eq_refl _) (eq_refl _)).
      Proof.
        - subst. simpl. blia.
        - subst. simpl. blia.
      Defined.
      
      Fixpoint predict_with_prefix prefix t predict_rest :=
        predict_with_prefix_body prefix t predict_rest predict_with_prefix.
      
      Lemma predict_with_prefix_works prefix predict_rest rest :
        (forall H, predicts (fun t => predict_rest (prefix ++ t) t (H t)) rest) ->
        predicts (fun t => predict_with_prefix prefix t (predict_rest t)) (prefix ++ rest).
      Proof.
        intros H. induction prefix.
        - simpl in H. simpl. apply H.
        - simpl. econstructor; [reflexivity|reflexivity|]. apply IHprefix. intros. apply H.
      Qed.
      
      Lemma predict_with_prefix_works_eq stuff prefix rest predict_rest :
        stuff = prefix ++ rest ->
        (forall H, predicts (fun t => predict_rest (prefix ++ t) t (H t)) rest) ->
        predicts (fun t => predict_with_prefix prefix t (predict_rest t)) stuff.
      Proof.
        intros H. subst. apply predict_with_prefix_works.
      Qed.
      
      Lemma predict_with_prefix_works_end prefix predict_rest :
        (forall H, predicts (fun t => predict_rest (prefix ++ t) t (H t)) []) ->
        predicts (fun t => predict_with_prefix prefix t (predict_rest t)) prefix.
      Proof.
        intros H. eapply predict_with_prefix_works in H. rewrite app_nil_r in H. eassumption.
      Qed.
      
      Lemma predict_with_prefix_ext x1 x2 f1 f2  :
        (forall y1 y2, f1 y1 y2 = f2 y1 y2) ->
        predict_with_prefix x1 x2 f1 = predict_with_prefix x1 x2 f2.
      Proof.
        intros. generalize dependent x2. induction x1.
        - intros. simpl. apply H.
        - intros. simpl. destruct x2; try reflexivity. apply IHx1. intros. apply H.
      Qed.

      Definition predict_with_prefix_valid prefix predict_rest :
        (forall e, In e prefix -> forall e', q e = q e' -> e = e') ->
        (forall H, predictor_valid prefix (fun k => predict_rest (prefix ++ k) k (H k))) ->
        predictor_valid [] (fun k => predict_with_prefix prefix k (predict_rest k)).
      Proof.
        intros H1 H2. induction prefix.
        - simpl in *. apply H2.
        - simpl. apply valid_cons. constructor. apply IHprefix. Abort.
      
      Lemma predict_cons e f t1 t2 :
        predicts f (t1 ++ e :: t2) ->
        f t1 = q e.
      Proof.
        clear. intros H. generalize dependent f. induction t1.
        - intros. simpl in H. inversion H. subst. assumption.
        - intros. simpl in H. inversion H. subst. rewrite H4. apply IHt1. assumption.
      Qed.
  End predictors.

  Definition s_predicts := predicts qend quot.
  Definition s_predicts_partly := predicts_partly quot.
  Definition s_predictor_valid := predictor_valid qend quot.
  
  Fixpoint predictor_of (a(*the whole thing*) : abstract_trace) (t(*so far*) : trace) : qevent :=
    match a, t with
    | _, nil =>
        match a with
        | empty => qend
        | aleak_unit _ => qleak_unit
        | aleak_bool b _ => qleak_bool b
        | aleak_word w _ => qleak_word w
        | aleak_list l _ => qleak_list l
        | aconsume_word _ => qconsume_word
        end
    | aleak_unit a', cons leak_unit t' => predictor_of a' t'
    | aleak_bool _ a', cons (leak_bool _) t' => predictor_of a' t'
    | aleak_word _ a', cons (leak_word _) t' => predictor_of a' t'
    | aleak_list _ a', cons (leak_list _) t' => predictor_of a' t'
    | aconsume_word f, cons (consume_word w) t' => predictor_of (f w) t'
    | _, _ => qend (*failure*)
    end.
  
  Lemma predictor_works a t :
    generates a t ->
    s_predicts (predictor_of a) t.
  Proof. intros H. induction H; intros; econstructor; simpl; eauto. Qed.

  Lemma predictor_of_valid a k :
    generates a k ->
    s_predictor_valid (rev k) (predictor_of a).
  Proof.
  Admitted.
(*    intros H. induction H.
    induction a; intros.
    - apply valid_nil. reflexivity.
    - apply valid_cons. intros. destruct e; try discriminate H. inversion IHa; subst.
      + econstructor. simpl. inversion IHa; subst.
      + simpl. apply valid_cons. intros. destruct e; try discriminate H0.
        constructor. assumption.
      + simpl. apply valid_cons. intros. destruct e; try discriminate H.
        constructor. assumption.
    - apply valid_cons. intros. simpl in H. destruct e; try discriminate H.
      simpl. assumption.
    - apply valid_cons. intros. simpl in H. destruct e; try discriminate H.
      simpl. assumption.
    - apply valid_cons. intros. simpl in H. destruct e; try discriminate H.
      simpl. assumption.
    - apply valid_cons. intros. simpl in H. destruct e; try discriminate H.
      simpl. apply X.
  Qed.*)
End WithIOEvent. (*maybe extend this to the end?*)
                            
  Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  io_trace -> mem -> String.string -> list word ->
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

Definition LeakExt {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far (idk when we'd need this, but why not allow it),
     the given-away memory, an action label and a list of function call arguments, *)
  io_trace -> mem -> String.string -> list word ->
  (* Gives the leakage of this external call. *)
  list word.

(*IDK if this should be here.*)
Existing Class LeakExt.

Section binops.
  Context {width : Z} {BW: Bitwidth width} {word : Word.Interface.word width}.
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
  Definition leak_binop (bop : bopname) (x1 : word) (x2 : word) : trace :=
    match bop with
    | bopname.divu | bopname.remu => cons (leak_word x2) (cons (leak_word x1) nil)
    | bopname.sru | bopname.slu | bopname.srs => cons (leak_word x2) nil
    | _ => nil
    end.
End binops.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.

  Local Notation metrics := MetricLog.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern).
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
      | expr.inlinetable aSize t index =>
          'Some (index', mc', tr') <- eval_expr index mc tr | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (
              v,
              (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc'))),
              leak_word index' :: tr')
      | expr.load aSize a =>
          'Some (a', mc', tr') <- eval_expr a mc tr | None;
          'Some v <- load aSize m a' | None;
          Some (
              v,
              addMetricInstructions 1 (addMetricLoads 2 mc'),
              leak_word a' :: tr')
      | expr.op op e1 e2 =>
          'Some (v1, mc', tr') <- eval_expr e1 mc tr | None;
          'Some (v2, mc'', tr'') <- eval_expr e2 mc' tr' | None;
          Some (
              interp_binop op v1 v2,
              addMetricInstructions 2 (addMetricLoads 2 mc''),
              leak_binop op v1 v2 ++ tr'')
      | expr.ite c e1 e2 =>
          'Some (vc, mc', tr') <- eval_expr c mc tr | None;
          eval_expr
            (if word.eqb vc (word.of_Z 0) then e2 else e1)
            (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc')))
            ((if word.eqb vc (word.of_Z 0) then leak_bool false else leak_bool true) :: tr')
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

    Lemma expr_to_other_trace e mc mc' k1 k1' v :
      eval_expr e mc k1 = Some (v, mc', k1') ->
      exists k'',
        k1' = k'' ++ k1 /\
          forall k2,
          eval_expr e mc k2 = Some (v, mc', k'' ++ k2).
    Proof.
      revert v. revert mc. revert k1. revert k1'. revert mc'. clear.
      induction e; intros ? ? ? ? ? H; simpl in H; try (inversion H; subst; clear H).
      - exists nil. auto.
      - destruct (map.get l x) as [v0|] eqn:E; [|congruence]. inversion H1; subst; clear H1.
        exists nil. simpl. rewrite E. auto.
      - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
        destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1. eapply IHe in E1. destruct E1 as [k'' [E1 E3] ]. subst.
        eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
      - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
        destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1. eapply IHe in E1. destruct E1 as [k'' [E1 E3] ]. subst.
        eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
      - destruct (eval_expr e1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        destruct (eval_expr e2 _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1.
        eapply IHe1 in E1. destruct E1 as [k''1 [H1 H2] ]. eapply IHe2 in E2.
        destruct E2 as [k''2 [H3 H4] ]. subst.
        eexists (_ ++ _ ++ _). repeat rewrite <- (app_assoc _ _ k1). intuition.
        simpl. rewrite H2. rewrite H4. f_equal. f_equal. repeat rewrite <- (app_assoc _ _ k2).
        reflexivity.
      - destruct (eval_expr e1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        eapply IHe1 in E1. destruct E1 as [k''1 [H2 H3] ]. subst. simpl.
        destruct (word.eqb _ _) eqn:E.
        + eapply IHe3 in H1. destruct H1 as [k''3 [H1 H2] ]. subst.
          eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
          intuition. rewrite H3. rewrite E. rewrite H2.
          repeat rewrite <- (app_assoc _ _ k2). reflexivity.
        + eapply IHe2 in H1. destruct H1 as [k''2 [H1 H2] ]. subst.
          eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
          intuition. rewrite H3. rewrite E. rewrite H2.
          repeat rewrite <- (app_assoc _ _ k2). reflexivity.
    Qed.

    Lemma call_args_to_other_trace arges mc k1 vs mc' k1' :
      evaluate_call_args_log arges mc k1 = Some (vs, mc', k1') ->
      exists k'',
        k1' = k'' ++ k1 /\
          forall k2,
            evaluate_call_args_log arges mc k2 = Some (vs, mc', k'' ++ k2).
    Proof.
      revert mc. revert k1. revert vs. revert mc'. revert k1'. induction arges; intros.
      - cbn [evaluate_call_args_log] in H. inversion H. subst.
        exists nil. intuition.
      - cbn [evaluate_call_args_log] in *.
        destruct (eval_expr _ _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        destruct (evaluate_call_args_log _ _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
        apply expr_to_other_trace in E1. apply IHarges in E2. fwd.
        eexists (_ ++ _).
        repeat rewrite <- (app_assoc _ _ k1). intuition. repeat rewrite <- (app_assoc _ _ k2).
        rewrite E1p1. rewrite E2p1. reflexivity.
    Qed.
    
  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context {leak_ext: LeakExt}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  (*I really want to do the semantics like this:
    cmd -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop.
    But it would be ugly.  Using app, screwing up simple postconditions
    (e.g., in seq case) in semantics.
    
    So I suppose I'll do 
    cmd -> trace -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop.
    
    Then we can state a lemma, saying that exec c nil t m l mc post -> exec c k t m l mc (fun k' => post (k' ++ k)).
    Then use that wherever we want, and it's *almost* like leakage trace isn't passed as a parameter to exec.
    Still ugly though.  But better?  No, not really.  Would be horribly obnoxious to apply that lemma.  Hm.

    I suppose I had better keep the append-style for leakage traces?  :(
    Is it still worthwhile to split up the io trace and leakage trace then?
    I think so.
    It still should be less of a pain to deal with them if they're separated.
   *)
  Inductive exec :
    cmd -> trace -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    k t m l mc post
    (_ : post k t m l mc)
    : exec cmd.skip k t m l mc post
  | set x e
    m l mc post
    k t v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : post k' t m (map.put l x v) (addMetricInstructions 1
                                      (addMetricLoads 1 mc')))
    : exec (cmd.set x e) k t m l mc post
  | unset x
    k t m l mc post
    (_ : post k t m (map.remove l x) mc)
    : exec (cmd.unset x) k t m l mc post
  | store sz ea ev
    k t m l mc post
    a mc' k' (_ : eval_expr m l ea mc k = Some (a, mc', k'))
    v mc'' k'' (_ : eval_expr m l ev mc' k' = Some (v, mc'', k''))
    m' (_ : store sz m a v = Some m')
    (_ : post (leak_word a :: k'') t m' l (addMetricInstructions 1
                                             (addMetricLoads 1
                                                (addMetricStores 1 mc''))))
    : exec (cmd.store sz ea ev) k t m l mc post
  | stackalloc x n body
    k t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body (consume_word a :: k) t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
          (fun k' t' mCombined' l' mc' =>
             exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post k' t' mSmall' l' mc'))
    : exec (cmd.stackalloc x n body) k t mSmall l mc post
  | if_true k t m l mc e c1 c2 post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 (leak_bool true :: k') t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | if_false e c1 c2
    k t m l mc post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 (leak_bool false :: k') t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | seq c1 c2
    k t m l mc post
    mid (_ : exec c1 k t m l mc mid)
    (_ : forall k' t' m' l' mc', mid k' t' m' l' mc' -> exec c2 k' t' m' l' mc' post)
    : exec (cmd.seq c1 c2) k t m l mc post
  | while_false e c
    k t m l mc post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : post (leak_bool false :: k') t m l (addMetricInstructions 1
                                                (addMetricLoads 1
                                                   (addMetricJumps 1 mc'))))
    : exec (cmd.while e c) k t m l mc post
  | while_true e c
      k t m l mc post
      v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c (leak_bool true :: k') t m l mc' mid)
      (_ : forall k'' t' m' l' mc'', mid k'' t' m' l' mc'' ->
                                      exec (cmd.while e c) k'' t' m' l' (addMetricInstructions 2
                                                                           (addMetricLoads 2
                                                                              (addMetricJumps 1 mc''))) post)
    : exec (cmd.while e c) k t m l mc post
  | call binds fname arges
      k t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' k' (_ : evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody (leak_unit :: k') t m lf (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc')))) mid)
      (_ : forall k'' t' m' st1 mc'', mid k'' t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post k'' t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))))
    : exec (cmd.call binds fname arges) k t m l mc post
  | interact binds action arges
      k t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' k' (_ :  evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list (leak_ext t mGive action args) :: k')%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l'
            (addMetricInstructions 1
               (addMetricStores 1
                  (addMetricLoads 2 mc'))))
    : exec (cmd.interact binds action arges) k t m l mc post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken: forall s k t m l mc post1,
      exec s k t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> _ -> Prop,
        (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
        exec s k t m l mc post2.
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

  Lemma intersect: forall k t l m mc s post1,
      exec s k t m l mc post1 ->
      forall post2,
        exec s k t m l mc post2 ->
        exec s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
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
      rename H0 into Ex1, H13 into Ex2.
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
      + eapply IHexec. exact H17. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H18 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.unique_mGive_footprint as P.
      specialize P with (1 := H1) (2 := H15).
      destruct (map.split_diff P H H7). subst mKeep0 mGive0. clear H7.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H15 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  Lemma exec_to_other_trace s k1 k2 t m l mc post :
    exec s k1 t m l mc post ->
    exec s k2 t m l mc (fun k2' t' m' l' mc' =>
                          exists k'',
                            k2' = k'' ++ k2 /\
                              post (k'' ++ k1) t' m' l' mc').
  Proof.
    intros H. generalize dependent k2. induction H; intros.
    - econstructor. exists nil. eauto.
    - apply expr_to_other_trace in H. destruct H as [k'' [H1 H2] ]. subst.
      econstructor; intuition eauto.
    - econstructor; intuition. exists nil. intuition.
    - apply expr_to_other_trace in H. apply expr_to_other_trace in H0.
      destruct H as [k''a [H3 H4] ]. subst. destruct H0 as [k''v [H5 H6] ]. subst.
      econstructor; intuition eauto. eexists (_ :: _ ++ _). simpl.
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. exists mSmall', mStack'. intuition. eexists (_ ++ _ :: nil).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_true; intuition eauto.
      eapply weaken. 1: eapply IHexec. simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_false; intuition.
      eapply weaken. 1: eapply IHexec. simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. fwd. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. eexists (_ ++ _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_false; intuition.
      eexists (_ :: _). intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_true; intuition. fwd.
      eapply weaken. 1: eapply H3; eauto. simpl. intros. fwd. eexists (_ ++ _ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - Search evaluate_call_args_log. apply call_args_to_other_trace in H0.
      fwd. econstructor; intuition eauto. fwd. apply H3 in H0p2.
      fwd. exists retvs. intuition. exists l'. intuition. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0. fwd. econstructor; intuition eauto.
      apply H2 in H0. fwd. exists l'. intuition. eexists (_ :: _).
      intuition.
  Qed.
      
  End WithEnv.
End exec. Notation exec := exec.exec.

