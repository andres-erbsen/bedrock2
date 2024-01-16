Require Import compiler.util.Common.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.MapEauto.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Registers.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatImpConstraints.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Tactics.fwd.
Require bedrock2.ProgramLogic.

Notation trace := Semantics.trace.
Notation leak_unit := Semantics.leak_unit.
Notation leak_bool := Semantics.leak_bool.
Notation leak_word := Semantics.leak_word.
Notation leak_list := Semantics.leak_list.
Notation consume_word := Semantics.consume_word.

Open Scope Z_scope.

Check Fix.

Section Spilling.

  Notation stmt := (stmt Z).

  Definition zero := 0.
  Definition ra := 1.
  Definition sp := 2.
  Definition gp := 3. (* we don't use the global pointer *)
  Definition tp := 4. (* we don't use the thread pointer *)
  Definition fp := 5. (* returned by stackalloc, always a constant away from sp: a wasted register *)
  Definition a0 := 10. (* first argument register *)
  Definition a7 := 17. (* last argument register *)

  (* `i=1 \/ i=2`, we use the argument registers as temporaries for spilling *)
  Definition spill_tmp(i: Z) := 9 + i.

  (* TODO: storing value returned by stackalloc into a register is always a wasted register,
     because it's constant away from the stackpointer *)

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte} {mem_ok: map.ok mem}.
  
  Definition stack_loc(r: Z): option Z :=
    if Z.leb 32 r then Some ((r - 32) * bytes_per_word) else None.

  (* argument/result registers for individual instructions (as opposed to for function calls) *)
  Definition iarg_reg(i r: Z): Z := if Z.leb 32 r then spill_tmp i else r.
  Definition ires_reg(r: Z): Z := if Z.leb 32 r then spill_tmp 1 else r.

  (* argument/result registers for function calls, `0 <= i < 8` *)
  Definition carg_reg(i: Z): Z := a0 + i.

  (* i needs to be 1 or 2, r any register > fp *)
  Definition load_iarg_reg(i r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word (9 + i) fp o
    | None => SSkip
    end.

  Definition leak_load_iarg_reg(fpval: word) (r: Z): trace :=
    match stack_loc r with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Definition save_ires_reg(r: Z): stmt :=
    match stack_loc r with
    | Some o => SStore Syntax.access_size.word fp (spill_tmp 1) o
    | None => SSkip
    end.

  Definition leak_save_ires_reg(fpval: word) (r: Z) : trace :=
    match stack_loc r with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Notation "s1 ;; s2" := (SSeq s1 s2) (right associativity, at level 60).

  (* reg must be <32, var might be >= 32 *)
  Definition set_reg_to_var(reg var: Z): stmt :=
    match stack_loc var with
    | Some o => SLoad Syntax.access_size.word reg fp o
    | None => SSet reg var
    end.

  Definition leak_set_reg_to_var(fpval: word) (var: Z) : trace :=
    match stack_loc var with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Fixpoint set_reg_range_to_vars(range_start: Z)(srcs: list Z): stmt :=
    match srcs with
    | nil => SSkip
    | x :: xs => set_reg_range_to_vars (range_start+1) xs;; set_reg_to_var range_start x
    end.

  Fixpoint leak_set_reg_range_to_vars(fpval: word)(srcs: list Z) : trace :=
    match srcs with
    | nil => nil
    | x :: xs => leak_set_reg_range_to_vars fpval xs ++ (leak_set_reg_to_var fpval x)
    end.

  (* var might be >=32, reg must be < 32 *)
  Definition set_var_to_reg(var reg: Z): stmt :=
    match stack_loc var with
    | Some o => SStore Syntax.access_size.word fp reg o
    | None => SSet var reg
    end.

  Definition leak_set_var_to_reg(fpval: word) (var: Z) : trace :=
    match stack_loc var with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Fixpoint set_vars_to_reg_range(dests: list Z)(range_start: Z): stmt :=
    match dests with
    | nil => SSkip
    | x :: xs => set_var_to_reg x range_start;; set_vars_to_reg_range xs (range_start+1)
    end.

  Fixpoint leak_set_vars_to_reg_range(fpval: word) (dests: list Z) : trace :=
    match dests with
    | nil => nil
    | x :: xs => leak_set_var_to_reg fpval x ++ (leak_set_vars_to_reg_range fpval xs)
    end.

  Fixpoint set_vars_to_reg_range_tailrec(do_first: stmt)(dests: list Z)(range_start: Z): stmt :=
    match dests with
    | nil => do_first
    | x :: xs => set_vars_to_reg_range_tailrec
                   (do_first;; set_var_to_reg x range_start) xs (range_start+1)
    end.

  (*very unlikely that this is good for anything*)
  (*Fixpoint leak_set_vars_to_reg_range_tailrec(do_first: Semantics.trace)(fpval: word)(dests: list Z) : Semantics.trace :=
    match dests with
    | nil => do_first
    | x :: xs => leak_set_vars_to_reg_range_tailrec
                   (do_first ++ leak_set_var_to_reg fpval x) fpval xs
    end.*)

  Definition prepare_bcond(c: bcond Z): stmt :=
    match c with
    | CondBinary _ x y => load_iarg_reg 1 x;; load_iarg_reg 2 y
    | CondNez x => load_iarg_reg 1 x
    end.
  Print load_iarg_reg. (* fun i r : Z => ... *)
  Print leak_load_iarg_reg. (* fun (fpval : word) (r : Z) => ... *)

  Definition leak_prepare_bcond(fpval: word) (c: bcond Z) : trace :=
    match c with
    | CondBinary _ x y => leak_load_iarg_reg fpval x ++ (leak_load_iarg_reg fpval y)
    | CondNez x => leak_load_iarg_reg fpval x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (iarg_reg 1 x) (iarg_reg 2 y)
    | CondNez x => CondNez (iarg_reg 1 x)
    end.

  Definition leak_spill_bcond : trace :=
    nil.
  (*TODO: remove sz from source-level read/writes. it's useless, we already know it from branching 
    information. similarly, we could replace separate read/writes with just one rw constructor. 
    maybe that's too much though. we could be sillier yet and say that every element of the trace is an integer (word.unsigned for r/w/salloc, 1/0 for branches)*)

   (* for a constant-time program, we should have a function which, given all compiler decisions that have
      happened so far, returns the next element of the trace.*)
  Print Semantics.event.
  (* *)
  Notation event := Semantics.event.
  Notation io_trace := Semantics.io_trace.
  
  Fixpoint pop_elts (start : trace) (t : trace) : event(*first elt of start not exhausted*) + trace(*remaining part of trace after start exhausted*) :=
    match start, t with
    | _ :: start', _ :: t' => pop_elts start' t'
    | e :: start', nil => inl e
    | nil, _ => inr t
    end.

  Check Fix.

  Require Import Coq.Init.Wf Relation_Operators Wellfounded PeanoNat Lia.
  
  Definition silly_body ab (silly : forall cd, slexprod _ _ lt lt cd ab -> nat -> nat -> nat) (x y : nat) : nat.
    refine (
        let a := fst ab in (* using match here would require the convoy pattern *)
        let b := snd ab in (* to make sure the value is available in the lt proof *)
        if Nat.eq_dec b 0%nat (* except for values whose type fully specifies them *)
        then if Nat.eq_dec a 0%nat then 0%nat
             else S (S (silly (pred a, 42%nat) _ 5 6)%nat)
        else S (S (silly (a, pred b) _ 6 7)%nat)
      ).
    Proof.
      all : abstract (clear silly;
                      subst a; subst b; case ab as [a b]; cbv [fst snd] in *; (right||left); lia).
    Defined.

Definition silly_wf : well_founded _ :=
  Acc_intro_generator 128 (wf_slexprod _ _ _ _ Nat.lt_wf_0 Nat.lt_wf_0).

Definition silly : nat * nat -> nat -> nat -> nat := Fix silly_wf _ silly_body.
 Check silly.
Lemma silly_step x a b : ltac:(
  let t := eval cbv beta delta [silly_body] in
    (silly x a b = silly_body x (fun y _ => silly y) a b)
  in exact t).
Proof.
  cbv [silly]. Check Fix_eq. Search Fix. rewrite Fix_eq with (F:=silly_body); cbv [silly_body]; intros.
  1: repeat (case Nat.eq_dec; try congruence).
  1: repeat (case Nat.eq_dec; try congruence).
  1,2: intros; rewrite H; reflexivity.
Qed.
Opaque silly.

Lemma even_silly : forall ab x y, Nat.even (silly ab x y) = true.
Proof.
  induction ab as [(a&b)] using (well_founded_induction silly_wf).
  intros. rewrite silly_step. cbv zeta beta.
  repeat (case Nat.eq_dec as [|]); rewrite ?Nat.even_succ_succ, ?H; auto;
    (* duplciated... *) auto using silly_body_subproof, silly_body_subproof0.
Qed.

Compute silly (10, 0)%nat 5 5.
  
Notation qevent := Semantics.qevent. Search qevent.

  Notation quot := Semantics.quot.
  Notation qleak_unit := Semantics.qleak_unit.
  Notation qleak_bool := Semantics.qleak_bool.
  Notation qleak_word := Semantics.qleak_word.
  Notation qleak_list := Semantics.qleak_list.
  Notation qconsume := Semantics.qconsume.
  Notation qend := Semantics.qend.

  Notation predicts := Semantics.predicts.
  Notation predict_with_prefix := Semantics.predict_with_prefix.
  Notation predict_with_prefix_works := Semantics.predict_with_prefix_works.
  Notation predict_with_prefix_works_end := Semantics.predict_with_prefix_works_end.
  Print SStackalloc.

  
  Require Import Coq.Wellfounded.Lexicographic_Product.
  Require Import Relation_Operators.

  
  Definition predictor_of_end (prefix : trace) (t : trace) : option qevent :=
    match pop_elts prefix t with
    | inl e => Some (quot e)
    | inr t' => Some qend
    end.

    

  (*Inductive subexpression : stmt -> stmt -> Prop :=
  | SStackalloc_subexp : forall x1 x2 s, subexpression s (SStackalloc x1 x2 s).

  Lemma wf_subexpression : well_founded subexpression.
  Proof.
    cbv [well_founded]. intros a. induction a.
    all: try solve [constructor; intros ? H; inversion H].
    constructor. intros y H. inversion H. subst. assumption.
  Defined.      

  Definition stmt_lt :=
    clos_trans _ subexpression.

  Lemma wf_stmt_lt : well_founded stmt_lt.
  Proof.
    cbv [stmt_lt]. Search (well_founded (clos_trans _ _)).
    apply Transitive_Closure.wf_clos_trans.
    apply wf_subexpression.
  Defined. Check ltof.

  Definition list_lt : list nat -> list nat -> Prop := ltof _ (@length _).
  
  Lemma wf_list_lt : well_founded list_lt.
  Proof.
    cbv [list_lt]. Search well_founded. apply well_founded_ltof.
  Defined.
  
  Definition lt_tuple := slexprod _ _ list_lt stmt_lt.

  Lemma lt_tuple_wf : well_founded lt_tuple.
  Proof.
    apply wf_slexprod.
    - apply wf_list_lt.
    - apply wf_stmt_lt.
  Defined.
  
  Program Fixpoint make_stmt_or_list_smaller (l : list nat) (s : stmt) {measure (l, s) lt_tuple} :=
    match s with
    | SStackalloc _ _ body =>
        make_stmt_or_list_smaller l body
    | _ =>
        match l with
        | _ :: l' => make_stmt_or_list_smaller l' s
        | _ => 5
        end
    end.

  Next Obligation.
    right. cbv [stmt_lt]. apply t_step. constructor.
  Defined.
  Next Obligation.
    left. cbv [list_lt ltof]. simpl. blia.
  Defined.
  Next Obligation.
    apply Wf.measure_wf. apply lt_tuple_wf.
  Defined.

  Compute (make_stmt_or_list_smaller [] SSkip).

  Print make_stmt_or_list_smaller_func.
  Check @make_stmt_or_list_smaller.*)

  Lemma predict_with_prefix_ext x1 x2 f1 f2  :
    (forall y1 y2, f1 y1 y2 = f2 y1 y2) ->
    predict_with_prefix x1 x2 f1 = predict_with_prefix x1 x2 f2.
  Proof.
    intros. generalize dependent x2. induction x1.
    - intros. simpl. apply H.
    - intros. simpl. destruct x2; try reflexivity. apply IHx1. intros. apply H.
  Qed.
    
  Inductive subexpression : stmt -> stmt -> Prop :=
  | SStackalloc_subexp : forall x1 x2 s, subexpression s (SStackalloc x1 x2 s)
  | SIf_then_subexp : forall x1 x2 s, subexpression s (SIf x1 s x2)
  | SIf_else_subexp : forall x1 x2 s, subexpression s (SIf x1 x2 s)
  | SLoop_body1_subexp : forall x1 x2 s, subexpression s (SLoop s x1 x2)
  | SLoop_body2_subexp : forall x1 x2 s, subexpression s (SLoop x1 x2 s)
  | SSeq_body1_subexp : forall x1 s, subexpression s (SSeq s x1)
  | SSeq_body2_subexp : forall x1 s, subexpression s (SSeq x1 s).
  
  Lemma wf_subexpression : well_founded subexpression.
  Proof.
    cbv [well_founded]. intros a. induction a.
    all: constructor; intros ? H; inversion H; subst; assumption.
  Defined.

  Definition stmt_lt :=
    clos_trans _ subexpression.

  Lemma wf_stmt_lt : well_founded stmt_lt.
  Proof.
    cbv [stmt_lt].
    apply Transitive_Closure.wf_clos_trans.
    apply wf_subexpression.
  Defined.

  Definition trace_lt : trace -> trace -> Prop := ltof _ (@length _).
  
  Lemma wf_trace_lt : well_founded trace_lt.
  Proof.
    cbv [trace_lt]. apply well_founded_ltof.
  Defined.
  Check wf_inverse_image.
  Lemma wf_bool_lt : well_founded Bool.lt.
  Proof.
    cbv [well_founded]. intros a. destruct a.
    - constructor. intros b H. destruct b; simpl in H; try solve [destruct H].
      constructor. intros c H'. Print Bool.lt. destruct c; simpl in H'; try solve [destruct H'].
      congruence.
    - constructor. intros b H. destruct b; simpl in H; try solve [destruct H]. congruence.
  Defined.

  Search (bool -> bool -> Prop).
  Print slexprod. Search well_founded.
  Definition lt_tuple' := slexprod _ _ lt stmt_lt.

  (* because idk how to do dependent tuple nicely *)
  Inductive bigtuple :=
  | bt (sk_so_far : trace) (s : stmt) (k_so_far : trace) (fpval : word) (f : forall (k_so_far' sk_so_far' : trace), (length sk_so_far' <= length sk_so_far)%nat -> option qevent).
  
  Definition project_tuple (tup : bigtuple) : nat * stmt :=
    match tup with
    | bt sk_so_far s k_so_far fpval f => (length sk_so_far, s)
    end.
  Definition lt_tuple (x y : bigtuple) :=
    lt_tuple' (project_tuple x) (project_tuple y).    
  
  Lemma lt_tuple'_wf : well_founded lt_tuple'.
  Proof.
    apply wf_slexprod.
    - apply lt_wf.
    - apply wf_stmt_lt.
  Defined.

  Lemma lt_tuple_wf : well_founded lt_tuple.
  Proof.
    cbv [lt_tuple]. apply wf_inverse_image. apply lt_tuple'_wf.
  Defined.
  

  
  Section FixPoint.
    Variable A : Type.
    Variable R : A -> A -> Prop.
    Hypothesis Rwf : well_founded R.
    Variable P : Type. (* really I want to say that P gives one type for each equivalence class
                          of A wrt the equivalence relation E.  Not clear how to say this though.*)
    Variable F : forall x:A, (forall y:A, R y x -> P) -> P.
    Variable E : A -> A -> Prop.
        
    Fixpoint my_Fix_F (x:A) (a:Acc R x) : P :=
      F x (fun (y:A) (h:R y x) => my_Fix_F y (Acc_inv a h)).
    
    Scheme Acc_inv_dep := Induction for Acc Sort Prop.
    
    Lemma my_Fix_F_eq (x:A) (r:Acc R x) :
      F x (fun (y:A) (p:R y x) => my_Fix_F y (Acc_inv r p)) = my_Fix_F x r.
    Proof.
      destruct r using Acc_inv_dep; auto.
    Qed.
    
    Definition my_Fix (x:A) := my_Fix_F x (Rwf x).
    
    (** Proof that [well_founded_induction] satisfies the fixpoint equation.
        It requires an extra property of the functional *)
    
    Hypothesis
      F_ext :
      forall (x1 x2:A) (f1:forall y:A, R y x1 -> P) (f2:forall y:A, R y x2 -> P),
        E x1 x2 ->
        (forall (y1 y2:A) (p1:R y1 x1) (p2:R y2 x2),
            E y1 y2 -> f1 y1 p1 = f2 y2 p2) -> F x1 f1 = F x2 f2.

    Lemma my_Fix_F_inv : forall (x1 x2:A) (r1:Acc R x1) (r2:Acc R x2),
        E x1 x2 -> my_Fix_F x1 r1 = my_Fix_F x2 r2.
    Proof.
      intro x1; induction (Rwf x1); intros x2 r1 r2.
      rewrite <- (my_Fix_F_eq x r1); rewrite <- (my_Fix_F_eq x2 r2); intros.
      apply F_ext; auto.
    Qed.

    Lemma my_Fix_eq : forall (x1 x2:A),
        E x1 x2 -> my_Fix x1 = F x2 (fun (y:A) (p:R y x2) => my_Fix y).
    Proof.
      intro x; unfold my_Fix.
      rewrite <- my_Fix_F_eq.
      intros. apply F_ext; intros.
      - assumption.
      - apply my_Fix_F_inv. assumption.
    Qed.

 End FixPoint.

  (*I have difficulty with Fix_eq (hard to prove funext property) if fix returns a function.*)
  Print existT.
  Check ({x:nat & 3 = 3}).
  Locate "{ : }".
  
  Definition snext_stmt'_body {env: map.map String.string (list Z * list Z * stmt)} (e: env) (next : trace -> option qevent)
    (tup : bigtuple)
    (snext_stmt' : forall othertuple, lt_tuple othertuple tup -> option qevent)
    : option qevent.
    refine (
        match tup as x return tup = x -> _ with
        | bt sk_so_far s k_so_far fpval f => fun _ => 
            match s as x return s = x -> _ with
            | SLoad sz x y o => fun _ => 
                                  match next k_so_far with
                                  | Some (qleak_word a) =>
                                      predict_with_prefix
                                        (leak_load_iarg_reg fpval y ++ [leak_word a] ++ leak_save_ires_reg fpval x)
                                        sk_so_far
                                        (fun sk_so_far' pf => f (k_so_far ++ [leak_word a]) sk_so_far' _)
                                  | _ => None
                                  end
            | SStore sz x y o => fun _ =>
                                   match next k_so_far with
                                   | Some (qleak_word a) =>
                                       predict_with_prefix
                                         (leak_load_iarg_reg fpval x ++ leak_load_iarg_reg fpval y ++ [leak_word a])
                                         sk_so_far
                                         (fun sk_so_far' pf => f (k_so_far ++ [leak_word a]) sk_so_far' _)
                                   | _ => None
                                   end
            | SInlinetable _ x _ i => fun _ =>
                                        match next k_so_far with
                                        | Some (qleak_word i') =>
                                            predict_with_prefix
                                              (leak_load_iarg_reg fpval i ++ [leak_word i'] ++ leak_save_ires_reg fpval x)
                                              sk_so_far
                                              (fun sk_so_far' pf => f (k_so_far ++ [leak_word i']) sk_so_far' _)
                                        | _ => None
                                        end
            | SStackalloc x _ body => fun _ =>
                                        match sk_so_far as x return sk_so_far = x -> option qevent with
                                        | consume_word a :: sk_so_far' => fun _ =>
                                                                            predict_with_prefix
                                                                              (leak_save_ires_reg fpval x)
                                                                              sk_so_far'
                                                                              (fun sk_so_far'' pf =>
                                                                                 snext_stmt'
                                                                                   (bt sk_so_far'' body (k_so_far ++ [consume_word a]) fpval
                                                                                      (fun k_so_far''' sk_so_far''' pf => f k_so_far''' sk_so_far'' _)) _)
                                        | nil => fun _ => Some qconsume
                                        | _ => fun _ => None
                                        end (eq_refl sk_so_far)
            | SLit x _ => fun _ =>
                            predict_with_prefix
                              (leak_save_ires_reg fpval x)
                              sk_so_far
                              (fun sk_so_far' pf => f k_so_far sk_so_far' _)
            | SOp x op y oz => fun _ =>
                                 let newt :=
                                   match op with
                                   | Syntax.bopname.divu
                                   | Syntax.bopname.remu =>
                                       match next k_so_far with
                                       | Some (qleak_word x1) =>
                                           match next (k_so_far ++ [leak_word x1]) with
                                           | Some (qleak_word x2) => Some [leak_word x1; leak_word x2]
                                           | _ => None
                                           end
                                       | _ => None
                                       end
                                   | Syntax.bopname.slu
                                   | Syntax.bopname.sru
                                   | Syntax.bopname.srs =>
                                       match next k_so_far with
                                       | Some (qleak_word x2) => Some [leak_word x2]
                                       | _ => None
                                       end
                                   | _ => Some []
                                   end
                                 in
                                 match newt with
                                 | Some newt =>
                                     predict_with_prefix
                                       (leak_load_iarg_reg fpval y ++
                                          match oz with 
                                          | Var z => leak_load_iarg_reg fpval z
                                          | Const _ => []
                                          end
                                          ++ newt
                                          ++ leak_save_ires_reg fpval x)
                                       sk_so_far
                                       (fun sk_so_far' pf => f (k_so_far ++ newt) sk_so_far' _)
                                 | None => None
                                 end
            | SSet x y => fun _ =>
                            predict_with_prefix
                              (leak_load_iarg_reg fpval y ++ leak_save_ires_reg fpval x)
                              sk_so_far
                              (fun sk_so_far' pf => f k_so_far sk_so_far' _)
            | SIf c thn els => fun _ =>
                                 match next k_so_far with
                                 | Some (qleak_bool b) =>
                                     predict_with_prefix
                                       (leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool b])
                                       sk_so_far
                                       (fun sk_so_far' pf =>
                                          snext_stmt'
                                            (bt sk_so_far' (if b then thn else els) (k_so_far ++ [leak_bool b]) fpval
                                               (fun k_so_far'' sk_so_far'' pf => f k_so_far'' sk_so_far'' _)) _)
                                 | _ => None
                                 end
            | SLoop s1 c s2 => fun _ =>
                                 snext_stmt'
                                   (bt sk_so_far s1 k_so_far fpval
                                     (fun k_so_far' sk_so_far' pf =>
                                        match next k_so_far' with
                                        | Some (qleak_bool true) =>
                                            predict_with_prefix
                                              (leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool true])
                                              sk_so_far'
                                              (fun sk_so_far'' pf =>
                                                 snext_stmt'
                                                   (bt sk_so_far'' s2 (k_so_far' ++ [leak_bool true]) fpval
                                                     (fun k_so_far'' sk_so_far''' pf =>
                                                        snext_stmt'
                                                          (bt sk_so_far''' s k_so_far'' fpval
                                                          (fun k_so_far''' sk_so_far'''' pf => f k_so_far''' sk_so_far'''' _)) _)) _)
                                        | Some (qleak_bool false) =>
                                            predict_with_prefix
                                              (leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool false])
                                              sk_so_far'
                                              (fun sk_so_far'' pf => f (k_so_far' ++ [leak_bool false]) sk_so_far'' _)
                                        | _ => None
                                        end)) _
            | SSeq s1 s2 => fun _ =>
                              snext_stmt'
                                (bt sk_so_far s1 k_so_far fpval
                                  (fun k_so_far' sk_so_far' pf =>
                                     snext_stmt'
                                       (bt sk_so_far' s2 k_so_far' fpval (fun k_so_far'' sk_so_far'' _ => f k_so_far'' sk_so_far'' _)) _)) _
            | SSkip => fun _ => f k_so_far sk_so_far _
            | SCall resvars fname argvars => fun _ =>
                                               match @map.get _ _ env e fname with
                                               | Some (params, rets, fbody) =>
                                                   predict_with_prefix
                                                     (leak_set_reg_range_to_vars fpval argvars ++ [leak_unit])
                                                     sk_so_far
                                                     (fun sk_so_far' pf =>
                                                        match sk_so_far' with (* would be nice if predict_with_prefix would do this *)
                                                        | consume_word fpval' :: sk_so_far'' =>
                                                            predict_with_prefix
                                                              (leak_set_vars_to_reg_range fpval' params)
                                                              sk_so_far''
                                                              (fun sk_so_far''' pf =>
                                                                 snext_stmt'
                                                                   (bt sk_so_far''' fbody (k_so_far ++ [leak_unit]) fpval'
                                                                     (fun k_so_far' sk_so_far'''' pf =>
                                                                        predict_with_prefix
                                                                          (leak_set_reg_range_to_vars fpval' rets ++ leak_set_vars_to_reg_range fpval resvars)
                                                                          sk_so_far''''
                                                                          (fun sk_so_far''''' pf => f k_so_far' sk_so_far''''' _))) _) 
                                                        | nil => Some qconsume
                                                        | _ => None
                                                        end)
                                               | None => None
                                               end
            | SInteract resvars _ argvars => fun _ =>
                                               match next k_so_far with
                                               | Some (qleak_list l) =>
                                                   predict_with_prefix
                                                     (leak_set_reg_range_to_vars fpval argvars ++ [leak_list l] ++ leak_set_vars_to_reg_range fpval resvars)
                                                     sk_so_far
                                                     (fun sk_so_far' pf => f (k_so_far ++ [leak_list l]) sk_so_far' _)
                                               | _ => None
                                               end
            end (eq_refl _)
      end (eq_refl _)).
    Proof.
      Unshelve.
      all: destruct sk_so_far__s__k_so_far__fpval__f as [ [ [ [ sk_so_far_ s_] k_so_far_] fpval_] f_].
      all: subst xx sk_so_far s k_so_far fpval f.
      all: cbn [fst snd] in *.
      all: cbv [lt_tuple project_tuple].
      all: repeat match goal with | H: _ |- _ => rewrite H end.
      - left. simpl. blia.
      - rewrite <- pf. repeat rewrite app_length. left. simpl. blia.
      - right. constructor. constructor.
      - right. constructor. constructor.
      - admit.
      - admit.
      - admit.
      - admit.
        right. constructor. constructor.
      - destruct (_ <? _)%nat eqn:E.
        + left. right. apply Nat.ltb_lt in E. cbv [trace_lt ltof]. blia.
        + left. left. reflexivity.
      - destruct (_ <? _)%nat eqn:E.
        + left. right. apply Nat.ltb_lt in E. cbv [trace_lt ltof]. blia.
        + left. left. reflexivity.
      - destruct (_ <? _)%nat eqn:E. Print Nat.ltb_lt.
        + apply Nat.ltb_lt in E. left. right. blia.
        + left. left. reflexivity.
      - destruct (_ <=? _)%nat eqn:E.
        + apply Nat.leb_le in E. Print Nat.eqb_eq.
          -- destruct (length sk_so_far' =? length sk_so_far_)%nat eqn:E'.
             ++ apply Nat.eqb_eq in E'. rewrite E'.
                right. constructor. constructor.
             ++ apply Nat.eqb_neq in E'. left. right. blia.
        + left. left. reflexivity.
    Defined.

    Check snext_stmt'_body.
    Check my_Fix.
    Definition snext_stmt'
      {env: map.map String.string (list Z * list Z * stmt)} e next
      := my_Fix _ _ lt_tuple_wf _ (snext_stmt'_body e next).

    Check snext_stmt'.
    Compute (snext_stmt' map.empty (fun _ => None) (false, [], SSkip, [], word.of_Z 0, (fun _ _ => None))).

    Definition Equiv (x y : bool * trace * stmt * trace * word * (trace -> trace -> option qevent)) :=
      let '(x1, x2, x3, x4, x5, fx) := x in
      let '(y1, y2, y3, y4, y5, fy) := y in
      (x1, x2, x3, x4, x5) = (y1, y2, y3, y4, y5) /\
        forall z1 z2, fx z1 z2 = fy z1 z2.

    Lemma snext_stmt'_step {env: map.map String.string (list Z * list Z * stmt)} e next bigtuple : ltac:(
                                     let t := eval cbv beta delta [snext_stmt'_body] in
                                     (snext_stmt' e next bigtuple = snext_stmt'_body e next bigtuple (fun y _ => snext_stmt' e next y))
                                       in exact t).
    Proof.
      cbv [snext_stmt']. Check Fix_eq. Search Fix. rewrite my_Fix_eq with (E:=Equiv) (x1:=bigtuple) (x2:=bigtuple) (F:=snext_stmt'_body e next).
      1: reflexivity.
      { intros. cbv [snext_stmt'_body]. cbv beta.
        destruct x1 as [ [ [ [ [live_1 sk_so_far_1] s_1] k_so_far_1] fpval_1] f_1].
        destruct x2 as [ [ [ [ [live_2 sk_so_far_2] s_2] k_so_far_2] fpval_2] f_2].
        cbn [fst snd].
        cbv [Equiv] in H. destruct H as [H1 H2]. injection H1. intros. subst. clear H1.
        repeat (Tactics.destruct_one_match; try reflexivity || apply predict_with_prefix_ext || apply H2 || intros || apply H0 || cbv [Equiiv]; intuition).
        all: cbv [Equiv]; intuition.
        all: repeat (Tactics.destruct_one_match; try reflexivity || apply predict_with_prefix_ext || apply H2 || intros || apply H0 || cbv [Equiv]; intuition).
        all: cbv [Equiv]; intuition.
        all: repeat (Tactics.destruct_one_match; try reflexivity || apply predict_with_prefix_ext || apply H2 || intros || apply H0 || cbv [Equiv]; intuition).
        all: cbv [Equiv]; intuition.
        all: repeat (Tactics.destruct_one_match; try reflexivity || apply predict_with_prefix_ext || apply H2 || intros || apply H0 || cbv [Equiv]; intuition).
        apply predict_with_prefix_ext. intros. apply H2. }
      { destruct bigtuple as [ [ [ [ [live_ sk_so_far_] s_] k_so_far_] fpval_] f_].
        cbv [Equiv]. intuition. }
    Qed.
    
  Definition snext_stmt {env : map.map string (list Z * list Z * stmt)} e next fpval s sk_so_far :=
    snext_stmt' e next (true, [], s, sk_so_far, fpval, (fun _ _ => Some qend)).
   
  Fixpoint spill_stmt(s: stmt): stmt :=
    match s with
    | SLoad sz x y o =>
      load_iarg_reg 1 y;;
      SLoad sz (ires_reg x) (iarg_reg 1 y) o;;
      save_ires_reg x
    | SStore sz x y o =>
      load_iarg_reg 1 x;; load_iarg_reg 2 y;;
      SStore sz (iarg_reg 1 x) (iarg_reg 2 y) o
    | SInlinetable sz x t i =>
      load_iarg_reg 2 i;;
      SInlinetable sz (ires_reg x) t (iarg_reg 2 i);;
      save_ires_reg x
    | SStackalloc x n body =>
      SStackalloc (ires_reg x) n (save_ires_reg x;; spill_stmt body)
    | SLit x n =>
      SLit (ires_reg x) n;;
      save_ires_reg x
    | SOp x op y oz => 
      load_iarg_reg 1 y;; 
      match oz with 
      | Var z => load_iarg_reg 2 z;; SOp (ires_reg x) op (iarg_reg 1 y) (Var (iarg_reg 2 z))
      | Const _ =>  SOp (ires_reg x) op (iarg_reg 1 y) oz
      end;; save_ires_reg x
    | SSet x y => (* TODO could be optimized if exactly one is on the stack *)
      load_iarg_reg 1 y;;
      SSet (ires_reg x) (iarg_reg 1 y);;
      save_ires_reg x
    | SIf c thn els =>
      prepare_bcond c;;
      SIf (spill_bcond c) (spill_stmt thn) (spill_stmt els)
    | SLoop s1 c s2 =>
      SLoop (spill_stmt s1;; prepare_bcond c) (spill_bcond c) (spill_stmt s2)
    | SSeq s1 s2 => SSeq (spill_stmt s1) (spill_stmt s2)
    | SSkip => SSkip
    | SCall resvars f argvars =>
      set_reg_range_to_vars a0 argvars;;
      SCall (List.firstn (length resvars) (reg_class.all reg_class.arg))
            f
            (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      set_vars_to_reg_range resvars a0
    | SInteract resvars f argvars =>
      set_reg_range_to_vars a0 argvars;;
      SInteract (List.firstn (length resvars) (reg_class.all reg_class.arg))
                f
                (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      set_vars_to_reg_range resvars a0
    end.

  Definition max_var_bcond(c: bcond Z): Z :=
    match c with
    | CondBinary _ x y => Z.max x y
    | CondNez x => x
    end.

  Fixpoint max_var(s: stmt): Z :=
    match s with
    | SLoad _ x y _ | SStore _ x y _ | SInlinetable _ x _ y | SSet x y => Z.max x y
    | SStackalloc x n body => Z.max x (max_var body)
    | SLit x _ => x
    | SOp x _ y oz => let vz := match oz with
                                | Var v => v
                                | Const _ => 0
                                end
                      in Z.max x (Z.max y vz)
    | SIf c s1 s2 | SLoop s1 c s2 => Z.max (max_var_bcond c) (Z.max (max_var s1) (max_var s2))
    | SSeq s1 s2 => Z.max (max_var s1) (max_var s2)
    | SSkip => 0
    | SCall resvars f argvars | SInteract resvars f argvars =>
      Z.max (List.fold_left Z.max argvars 0) (List.fold_left Z.max resvars 0)
    end.

  Lemma le_fold_left_max: forall l a init,
      a <= init ->
      a <= fold_left Z.max l init.
  Proof.
    induction l; simpl; intros.
    - assumption.
    - eapply IHl. apply Z.max_le_iff. left. assumption.
  Qed.

  Lemma le_fold_left_max_increase_init: forall l init1 init2,
      init1 <= init2 ->
      fold_left Z.max l init1 <= fold_left Z.max l init2.
  Proof.
    induction l; simpl; intros.
    - assumption.
    - eapply IHl. blia.
  Qed.

  Lemma Forall_le_max: forall (l: list Z), Forall (fun x : Z => x <= fold_left Z.max l 0) l.
  Proof.
    induction l; simpl.
    - constructor.
    - constructor.
      + apply le_fold_left_max. apply Z.le_max_r.
      + eapply Forall_impl. 2: exact IHl. cbv beta. intros.
        etransitivity. 1: exact H.
        eapply le_fold_left_max_increase_init.
        apply Z.le_max_l.
  Qed.

  Hint Extern 1 => blia : max_var_sound.
  Hint Extern 1 => cbv beta : max_var_sound.
  Hint Extern 1 => eapply Forall_vars_stmt_impl; cycle -1 : max_var_sound.
  Hint Resolve Forall_and : max_var_sound.
  Hint Extern 1 => eapply Forall_impl; [|eapply Forall_le_max]; cbv beta : max_var_sound.
  Hint Extern 1 => match goal with
                   | IH: forall _, _ -> Forall_vars_stmt _ _ _ |- Forall_vars_stmt _ _ _ =>
                     eapply IH
                   end : max_var_sound.

  Lemma max_var_sound: forall s,
      Forall_vars_stmt (fun x => fp < x /\ (x < a0 \/ a7 < x)) s ->
      Forall_vars_stmt (fun x => fp < x <= max_var s /\ (x < a0 \/ a7 < x)) s.
  Proof.
    induction s; simpl; intros; unfold ForallVars_bcond in *; simpl;
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | c: bcond _ |- _ => destruct c; simpl
             | |- _ /\ _ => split
             | y: operand |- _ => destruct y
             end;
      eauto 4 with max_var_sound.
    all: eapply Forall_and;
         [ eapply Forall_and;
           [ eapply Forall_impl; [|eassumption];
             cbv beta; intros; blia
           | eapply Forall_impl; [|eapply Forall_le_max];
             cbv beta; intros; blia ]
         | eapply Forall_impl; [|eassumption]; cbv beta; blia ].
  Qed.

  Open Scope bool_scope.

  Definition is_valid_src_var(x: Z): bool := Z.ltb fp x && (Z.ltb x a0 || Z.ltb a7 x). Check bytes_per_word.

  Definition spill_fun: list Z * list Z * stmt -> result (list Z * list Z * stmt) :=
    fun '(argnames, resnames, body) =>
      (* TODO these checks could also be put into Lang.(Valid), so that there are
         fewer reasons for the compiler to return None *)
      if List.forallb is_valid_src_var argnames &&
         List.forallb is_valid_src_var resnames &&
         forallb_vars_stmt is_valid_src_var body
      then
        if Nat.leb (List.length argnames) 8 && Nat.leb (List.length resnames) 8 then
          let argnames' := List.firstn (List.length argnames) (reg_class.all reg_class.arg) in
          let resnames' := List.firstn (List.length resnames) (reg_class.all reg_class.arg) in
          let maxvar := Z.max (max_var body)
                              (Z.max (fold_left Z.max argnames 0) (fold_left Z.max resnames 0)) in
          Success (argnames', resnames',
              (* `Z.of_nat (Z.to_nat _)` is to to make sure it's not negative.
              We might stackalloc 0 bytes, but that still writes fp, which is required to be
              set by `related`, and we don't want to complicate `related` to accommodate for a
              potentially uninitialized `fp` after a function call happens in a fresh locals env *)
              SStackalloc fp (bytes_per_word * Z.of_nat (Z.to_nat (maxvar - 31))) (
                set_vars_to_reg_range argnames a0;;
                spill_stmt body;;
                set_reg_range_to_vars a0 resnames
              ))
        else
          error:("Number of function arguments and return values must not exceed 8")
      else
        error:("Spilling got input program with invalid var names (please report as a bug)").

  Definition snext_fun {env : map.map string (list Z * list Z * stmt)} (e : env) (next : trace -> option qevent) (k_so_far : trace) (f : list Z * list Z * stmt) (sk_so_far : Semantics.trace) : option Semantics.qevent :=
    let '(argnames, resnames, body) := f in
    match sk_so_far with
    | [] => Some qconsume
    | consume_word fpval :: sk_so_far' =>
        predict_with_prefix
          (leak_set_vars_to_reg_range fpval argnames)
          (fun sk_so_far'' => snext_stmt' e next (true, k_so_far, body, sk_so_far'', fpval,
                                  (fun k_so_far' sk_so_far''' =>
                                     predict_with_prefix
                                       (leak_set_reg_range_to_vars fpval resnames)
                                       (fun sk_so_far'''' => match sk_so_far'''' with |nil => Some qend |_ => None end)
                                       sk_so_far''')))
          sk_so_far'
    | _ => None
    end.

  Lemma firstn_min_absorb_length_r{A: Type}: forall (l: list A) n,
      List.firstn (Nat.min n (length l)) l = List.firstn n l.
  Proof.
    intros. destruct (Nat.min_spec n (length l)) as [[? E] | [? E]]; rewrite E.
    - reflexivity.
    - rewrite List.firstn_all. rewrite List.firstn_all2 by assumption. reflexivity.
  Qed.

  Lemma set_reg_range_to_vars_uses_standard_arg_regs: forall args start,
      uses_standard_arg_regs (set_reg_range_to_vars start args).
  Proof.
    induction args; intros; cbn; unfold set_reg_to_var;
      repeat destruct_one_match; cbn; eauto.
  Qed.

  Lemma set_vars_to_reg_range_uses_standard_arg_regs: forall args start,
      uses_standard_arg_regs (set_vars_to_reg_range args start).
  Proof.
    induction args; intros; cbn; unfold set_var_to_reg;
      repeat destruct_one_match; cbn; eauto.
  Qed.

  Lemma spill_stmt_uses_standard_arg_regs: forall s, uses_standard_arg_regs (spill_stmt s).
  Proof.
    induction s; simpl; unfold prepare_bcond, load_iarg_reg, save_ires_reg;
      repeat destruct_one_match; simpl;
      rewrite ?List.firstn_length, ?firstn_min_absorb_length_r;
      eauto using set_reg_range_to_vars_uses_standard_arg_regs,
                  set_vars_to_reg_range_uses_standard_arg_regs.
  Qed.

  Context {locals: map.map Z word}.
  Context {localsOk: map.ok locals}.
  Context {env: map.map String.string (list Z * list Z * stmt)} {env_ok: map.ok env}.
  Context {ext_spec: Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context {leak_ext: Semantics.LeakExt}.

  Definition spill_functions: env -> result env :=
    map.try_map_values spill_fun.

  Definition valid_vars_src(maxvar: Z): stmt -> Prop :=
    Forall_vars_stmt (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)).

  Definition valid_vars_tgt: stmt -> Prop :=
    Forall_vars_stmt (fun x => 3 <= x < 32).

  Local Arguments Z.of_nat: simpl never.
  Local Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.

  Lemma set_vars_to_reg_range_valid_vars: forall args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x) args ->
      valid_vars_tgt (set_vars_to_reg_range args start).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + unfold set_var_to_reg, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
      + eapply IHargs; try blia. assumption.
  Qed.

  Lemma set_reg_range_to_vars_valid_vars: forall args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x) args ->
      valid_vars_tgt (set_reg_range_to_vars start args).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + eapply IHargs; try blia. assumption.
      + unfold set_reg_to_var, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
  Qed.

  Lemma spill_stmt_valid_vars: forall s m,
      max_var s <= m ->
      valid_vars_src m s ->
      valid_vars_tgt (spill_stmt s).
  Proof.
    
    unfold valid_vars_src, valid_vars_tgt.
    induction s; simpl; intros;
      repeat match goal with
             | c: bcond Z |- _ => destr c
             | z: operand |- _ => destruct z
             | |- context[Z.leb ?x ?y] => destr (Z.leb x y)
             | |- _ => progress simpl
             | |- _ => progress unfold spill_tmp, sp, fp, ires_reg, iarg_reg, iarg_reg, ires_reg,
                         spill_bcond, max_var_bcond, ForallVars_bcond, prepare_bcond,
                         load_iarg_reg, load_iarg_reg, save_ires_reg, stack_loc in *
             end;
      try blia;
      fwd;
      repeat match goal with
      | IH: _, H: Forall_vars_stmt _ _ |- _ =>
        specialize IH with (2 := H);
        match type of IH with
        | ?P -> _ => let A := fresh in assert P as A by blia; specialize (IH A); clear A
        end
      end; eauto;   intuition try blia;
      try eapply set_reg_range_to_vars_valid_vars;
      try eapply set_vars_to_reg_range_valid_vars;
      unfold a0, a7 in *;
      eauto;
      rewrite ?List.firstn_length;
      try eapply List.Forall_firstn;
      try (eapply List.Forall_impl; [|eapply arg_range_Forall]; cbv beta);
      try blia;
      (eapply Forall_impl; [|eassumption]); cbv beta; unfold fp; blia.
  Qed.

  (* potentially uninitialized argument registers (used also as spilling temporaries) *)
  Definition arg_regs(l: locals): Prop :=
    forall k v, map.get l k = Some v -> 10 <= k < 18.

  Definition related(maxvar: Z)(frame: mem -> Prop)(fpval: word)
             (t1: Semantics.io_trace)(m1: mem)(l1: locals)
             (t2: Semantics.io_trace)(m2: mem)(l2: locals): Prop :=
      exists lStack lRegs stackwords,
        t1 = t2 /\
        (eq m1 * word_array fpval stackwords * frame)%sep m2 /\
        (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) /\
        (forall x v, map.get lStack x = Some v -> 32 <= x <= maxvar) /\
        (eq lRegs * eq lStack)%sep l1 /\
        (eq lRegs * arg_regs * ptsto fp fpval)%sep l2 /\
        (forall r, 32 <= r <= maxvar -> forall v, map.get lStack r = Some v ->
           nth_error stackwords (Z.to_nat (r - 32)) = Some v) /\
        length stackwords = Z.to_nat (maxvar - 31).

  Implicit Types post : Semantics.trace -> Semantics.io_trace -> mem -> locals -> MetricLog -> Prop.

  Lemma put_arg_reg: forall l r v fpval lRegs,
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      a0 <= r <= a7 ->
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep (map.put l r v).
  Proof.
    intros.
    assert (((eq lRegs * ptsto fp fpval) * arg_regs)%sep l) as A by ecancel_assumption. clear H.
    enough (((eq lRegs * ptsto fp fpval) * arg_regs)%sep (map.put l r v)). 1: ecancel_assumption.
    unfold sep at 1. unfold sep at 1 in A. fwd.
    unfold arg_regs in *.
    unfold map.split.
    unfold map.split in Ap0. fwd.
    exists mp, (map.put mq r v). ssplit.
    - apply map.put_putmany_commute.
    - unfold sep, map.split in Ap1. fwd. unfold map.disjoint in *.
      intros. rewrite map.get_put_dec in H2. rewrite map.get_putmany_dec in H.
      unfold ptsto in *. subst.
      setoid_rewrite map.get_put_dec in Ap1p0p1. setoid_rewrite map.get_empty in Ap1p0p1.
      setoid_rewrite <- map.put_putmany_commute in Ap0p1.
      setoid_rewrite map.putmany_empty_r in Ap0p1.
      setoid_rewrite map.get_put_dec in Ap0p1.
      rewrite map.get_put_dec in H. rewrite map.get_empty in H. unfold fp, spill_tmp, a0, a7 in *.
      specialize (Ap0p1 k).
      destruct_one_match_hyp; fwd; subst; destruct_one_match_hyp; fwd; subst.
      + blia.
      + specialize H1 with (1 := H). blia.
      + eauto.
      + eauto.
    - assumption.
    - intros. rewrite map.get_put_dec in H. unfold spill_tmp, a0, a7 in *.
      destruct_one_match_hyp.
      + blia.
      + eauto.
  Qed.

  Lemma put_tmp: forall l i v fpval lRegs,
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      i = 1 \/ i = 2 ->
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep (map.put l (spill_tmp i) v).
  Proof.
    intros. assert (a0 <= spill_tmp i <= a7) by (unfold spill_tmp, a0, a7; blia).
    unfold spill_tmp. eapply put_arg_reg; eassumption.
  Qed.

  Lemma load_iarg_reg_correct(i: Z): forall r e2 k2 t1 t2 m1 m2 l1 l2 mc2 fpval post frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      (forall mc2,
          let k2' := rev (leak_load_iarg_reg fpval r) ++ k2 in
          related maxvar frame fpval t1 m1 l1 t2 m2 (map.put l2 (iarg_reg i r) v) ->
          post k2' t2 m2 (map.put l2 (iarg_reg i r) v) mc2) ->
      exec e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2 post.
  Proof.
    intros.
    unfold leak_load_iarg_reg, load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + eapply H3.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p5|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      eapply H3.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  Lemma load_iarg_reg_correct'(i: Z): forall r e2 k1 k2 t1 t2 m1 m2 l1 l2 mc1 mc2 post frame maxvar v fpval,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      post k1 t1 m1 l1 mc1 ->
      exec e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2
        (fun k2' t2' m2' l2' mc2' => exists k1' t1' m1' l1' mc1',
             related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\ post k1' t1' m1' l1' mc1').
  Proof.
    intros.
    unfold load_iarg_reg, leak_load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p5|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  (* Note: if we wanted to use this lemma in subgoals created by exec.loop,
     new postcondition must not mention the original t2, m2, l2, mc2, (even though
     it would be handy to just say t2'=t2, m2=m2', l2' = map.put l2 (iarg_reg i r) v), because
     when the new postcondition is used as a "mid1" in exec.loop, and body1 is a seq
     in which this lemma was used, t2, m2, l2, mc2 are introduced after the evar "?mid1"
     is created (i.e. after exec.loop is applied), so they are not in the scope of "?mid1". *)
  Lemma load_iarg_reg_correct''(i: Z): forall r e2 k2 t1 t2 m1 m2 l1 l2 mc2 frame maxvar v fpval,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      exec e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2 (fun k2' t2' m2' l2' mc2' =>
      k2' = rev (leak_load_iarg_reg fpval r) ++ k2
      /\ m2' = m2 /\ l2' = map.put l2 (iarg_reg i r) v /\
        related maxvar frame fpval t1 m1 l1 t2' m2' l2').
  Proof.
    intros.
    unfold load_iarg_reg, leak_load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      assert (l2 = map.put l2 r v) as F. {
        symmetry. apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_ires_reg_correct: forall e k1 k2 t1 t2 m1 m2 l1 l2 mc1 mc2 x v maxvar frame post fpval,
      post k1 t1 m1 (map.put l1 x v) mc1 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      exec e (save_ires_reg x) k2 t2 m2 (map.put l2 (ires_reg x) v) mc2
        (fun k2' t2' m2' l2' mc2' => exists k1' t1' m1' l1' mc1',
                related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\ post k1' t1' m1' l1' mc1').
  Proof.
    intros.
    unfold save_ires_reg, stack_loc, ires_reg, related in *. fwd.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          9: eassumption.
          1: reflexivity.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in H0p3|-*.
            destruct H0p4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize H0p2 with (1 := H0).
              rewrite map.get_put_dec in H1. destr (x =? k).
              + blia.
              + specialize H0p3 with (1 := H1). blia.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H0. destr (x =? x0).
            - blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H1. destr (x =? r).
            - apply Option.eq_of_eq_Some in H1. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { unfold spill_tmp. eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      9: eassumption.
      1: reflexivity.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in H0p4.
        unfold sep, map.split in H0p3|-*.
        destruct H0p4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize H0p3 with (1 := H0).
          rewrite map.get_put_dec in H1. destr (x =? k).
          + blia.
          + specialize H0p2 with (1 := H1). blia.
      }
      1: {
        intros. rewrite map.get_put_dec in H0. destr (x =? x0).
        - blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        unfold arg_regs, sep, map.split, spill_tmp, fp, a0, a7 in *.
        intros. fwd.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H1.
        repeat destruct_one_match_hyp; subst; fwd; try congruence; try blia.
        specialize H0p8 with (1 := H1). blia.
      }
      all: try eassumption.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_ires_reg_correct'': forall e k2 t1 t2 m1 m2 l1 l2 mc2 x v maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      (forall t2' m2' l2' mc2',
          let k2' := rev (leak_save_ires_reg fpval x) ++ k2 in
          related maxvar frame fpval t1 m1 (map.put l1 x v) t2' m2' l2' ->
          post k2' t2' m2' l2' mc2') ->
      exec e (save_ires_reg x) k2 t2 m2 (map.put l2 (ires_reg x) v) mc2 post.
  Proof.
    intros.
    unfold leak_save_ires_reg, save_ires_reg, stack_loc, ires_reg, related in *. fwd.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - eapply H1.
          repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          1: reflexivity.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in Hp3|-*.
            destruct Hp4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize Hp2 with (1 := H).
              rewrite map.get_put_dec in H0. destr (x =? k).
              + blia.
              + eauto with zarith.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H. destr (x =? x0).
            - blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H0. destr (x =? r).
            - apply Option.eq_of_eq_Some in H0. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { unfold spill_tmp. eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      eapply H1.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1: reflexivity.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in Hp4.
        unfold sep, map.split in Hp4|-*.
        destruct Hp4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize Hp3 with (1 := H).
          rewrite map.get_put_dec in H0. destr (x =? k).
          + blia.
          + eauto with zarith.
      }
      1: {
        intros. rewrite map.get_put_dec in H. destr (x =? x0).
        - blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        unfold arg_regs, sep, map.split, spill_tmp, fp, a0, a7 in *.
        intros. fwd.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H0.
        repeat destruct_one_match_hyp; subst; fwd; try congruence; try blia.
        specialize Hp8 with (1 := H0). blia.
      }
      all: try eassumption.
  Qed.

  Lemma get_iarg_reg_1: forall l l2 y y' (z : Z) (z' : word),
      fp < y /\ (y < a0 \/ a7 < y) ->
      fp < z /\ (z < a0 \/ a7 < z) ->
      map.get l y = Some y' ->
      map.get l z = Some z' ->
      map.get (map.put (map.put l2 (iarg_reg 1 y) y') (iarg_reg 2 z) z') (iarg_reg 1 y) = Some y'.
  Proof.
    intros.
    destr (y =? z).
    - replace z' with y' in * by congruence.
      unfold iarg_reg, spill_tmp. destruct_one_match.
      + rewrite map.get_put_diff by blia. rewrite map.get_put_same. reflexivity.
      + rewrite map.get_put_same. reflexivity.
    - rewrite map.get_put_diff.
      + rewrite map.get_put_same. reflexivity.
      + unfold iarg_reg, spill_tmp, a0, a7, fp in *. repeat destruct_one_match; blia.
  Qed.

  (* Need to repeat in each section because autorewrite does not run typeclass search to
     find key_eqb_spec *)
  Hint Rewrite
       (sep_eq_empty_l (key_eqb := Z.eqb))
       (sep_eq_empty_r (key_eqb := Z.eqb))
    : fwd_rewrites.

  Lemma hide_ll_arg_reg_ptsto_core: forall k v R l,
      (arg_regs * ptsto k v * R)%sep l ->
      10 <= k < 18 ->
      (arg_regs * R)%sep l.
  Proof.
    unfold arg_regs, sep, ptsto, map.split. intros. fwd.
    exists (map.putmany mp0 (map.put map.empty k v)), mq. ssplit; auto.
    intros. rewrite map.get_putmany_dec, map.get_put_dec, map.get_empty in H.
    destr (k =? k0); subst; fwd; eauto.
  Qed.

  Lemma hide_ll_arg_reg_ptsto: forall k v P R l,
      iff1 (arg_regs * R)%sep P ->
      (arg_regs * ptsto k v * R)%sep l ->
      10 <= k < 18 ->
      P l.
  Proof.
    intros. apply H. eapply hide_ll_arg_reg_ptsto_core; eassumption.
  Qed.

  Lemma set_vars_to_reg_range_correct:
    forall args start argvs e k2 t1 t2 m1 m2 l1 l1' l2 mc2 maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      map.putmany_of_list_zip args argvs l1 = Some l1' ->
      map.getmany_of_list l2 (List.unfoldn (Z.add 1) (List.length args) start) = Some argvs ->
      (List.length args <= 8)%nat ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      (forall t2' m2' l2' mc2',
          let k2' := rev (leak_set_vars_to_reg_range fpval args) ++ k2 in
          related maxvar frame fpval t1 m1 l1' t2' m2' l2' ->
          post k2' t2' m2' l2' mc2') ->
      exec e (set_vars_to_reg_range args start) k2 t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. fwd. eauto.
    - simpl. unfold set_var_to_reg, stack_loc.
      unfold related in H. fwd.
      eapply exec.seq_cps.
      rewrite (Z.add_comm 1 start) in *.
      simpl in H6. cbv [leak_set_var_to_reg stack_loc] in H6.
      destr (32 <=? a).
      + edestruct store_to_word_array with (i := a - 32).
        1: ecancel_assumption. 1: blia.
        fwd.
        eapply exec.store.
        { eapply get_sep. ecancel_assumption. }
        { eassumption. }
        { eassumption. } Search (rev (_ ++ _)).
        rewrite rev_app_distr in H6. cbn [rev] in H6.
        repeat rewrite <- List.app_assoc in H6. cbn [List.app] in H6.
        eapply IHargs; try eassumption; try blia.
        (* establish related for IH: *)
        unfold related.
        eexists (map.put lStack a v), lRegs, _.
        ssplit.
        { reflexivity. }
        { ecancel_assumption. }
        { eassumption. }
        { intros. rewrite map.get_put_dec in H. destr (a =? x0). 1: blia. eauto. }
        { apply sep_comm. eapply sep_eq_put. 1: apply sep_comm; assumption.
          intros lRegs' w ? G. subst lRegs'.
          match goal with H: _ |- _ => specialize H with (1 := G) end. blia. }
        { eassumption. }
        { intros b A0 w B0.
          rewrite map.get_put_dec in B0.
          destr (a =? b). 1: congruence.
          match goal with H: _ |- _ => eapply H end. 1: blia.
          match goal with H: _ |- _ => eapply H end. 1: blia.
          assumption. }
        { blia. }
      + eapply exec.set.
        { eassumption. }
        eapply IHargs; try eassumption; try blia. 2: {
          eapply map.getmany_of_list_put_diff. 2: eassumption.
          eapply List.not_In_Z_seq. blia.
        }
        unfold related. eexists lStack, (map.put lRegs a v), _.
        ssplit.
        { reflexivity. }
        { ecancel_assumption. }
        { intros. rewrite map.get_put_dec in H. destr (a =? x). 1: blia. eauto. }
        { eassumption. }
        { eapply sep_eq_put. 1: assumption.
          intros lStack' w ? G. subst lStack'.
          match goal with H: _ |- _ => specialize H with (1 := G) end. blia. }
        { apply sep_assoc. eapply sep_eq_put. 1: ecancel_assumption.
          unfold ptsto, arg_regs.
          intros l w (l_arg_regs & l_fpval & (? & ?) & ? & ?) G. subst.
          rewrite map.get_putmany_dec, map.get_put_dec, map.get_empty in G.
          destr (fp =? a). 1: unfold fp; blia.
          match goal with H: _ |- _ => specialize H with (1 := G) end.
          unfold a0, a7 in *. blia. }
        { assumption. }
        { assumption. }
  Qed.

  Lemma set_reg_range_to_vars_correct:
    forall args argvs start e k2 t1 t2 m1 m2 l1 l2 mc2 maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      (List.length args <= 8)%nat ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      map.getmany_of_list l1 args = Some argvs ->
      (forall t2' l2' mc2',
          let k2' := rev (leak_set_reg_range_to_vars fpval args) ++ k2 in
          related maxvar frame fpval t1 m1 l1 t2' m2 l2' ->
          map.getmany_of_list l2' (List.unfoldn (Z.add 1) (List.length args) start) = Some argvs ->
          post k2' t2' m2 l2' mc2') ->
      exec e (set_reg_range_to_vars start args) k2 t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. eapply H5. 1: eassumption. simpl.
      destruct argvs. 1: reflexivity. discriminate.
    - simpl. unfold set_reg_to_var, leak_set_reg_to_var, stack_loc.
      destruct argvs as [|v vs]. {
        unfold map.getmany_of_list in H4. cbn in H4. simp.
        destr (List.option_all (map (map.get l1) args)); discriminate.
      }
      eapply map.invert_getmany_of_list_cons in H4. destruct H4 as [G GM].
      cbn [List.length] in *.
      simp.
      cbn [leak_set_reg_range_to_vars] in H5. cbv [leak_set_reg_to_var stack_loc] in H5.
      destr (32 <=? a).
      + eapply exec.seq_cps.
        eapply IHargs; try eassumption; try blia.

        intros.
        unfold related in H3. simp.
        eapply exec.load.
        * eapply get_sep. ecancel_assumption.
        * eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
          eapply H3p5. 1: blia.
          unfold sep in H3p3. simp.
          eapply map.get_split_r. 1,3: eassumption.
          destr (map.get mp a); [exfalso|reflexivity].
          specialize H3p1 with (1 := E0). blia.
        * rewrite rev_app_distr in H5. rewrite <- List.app_assoc in H5. cbn [rev List.app] in H5.
          eapply H5.
          -- unfold related.
             repeat match goal with
                    | |- exists _, _ => eexists
                    | |- _ /\ _ => split
                    | |- _ => eassumption || reflexivity
                    | |- _ => f_equal
                    end.
             eapply put_arg_reg; try eassumption. blia.
          -- cbn [List.unfoldn]. eapply map.getmany_of_list_cons.
             ++ apply map.get_put_same.
             ++ rewrite Z.add_comm.
                eapply map.getmany_of_list_put_diff. 2: eassumption.
                eauto using List.not_In_Z_seq with zarith.
      + eapply exec.seq_cps.
        eapply IHargs; try eassumption; try blia.
        intros.
        unfold related in H3. simp.
        eapply exec.set.
        * edestruct (eq_sep_to_split l2') as (l2Rest & S22 & SP22). 1: ecancel_assumption.
          eapply map.get_split_grow_r. 1: eassumption.
          unfold sep in H3p3. destruct H3p3 as (lRegs' & lStack' & S2 & ? & ?).
          subst lRegs' lStack'.
          eapply map.get_split_l. 1: exact S2. 2: exact G.
          destr (map.get lStack a); [exfalso|reflexivity].
          specialize H3p2 with (1 := E0). blia.
        * rewrite app_nil_r in H5. eapply H5. 2: {
            cbn [List.unfoldn].
            eapply map.getmany_of_list_cons.
            - apply map.get_put_same.
            - rewrite Z.add_comm. eapply map.getmany_of_list_put_diff. 2: eassumption.
              eauto using List.not_In_Z_seq with zarith.
          }
          unfold related.
          repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 | |- _ => eassumption || reflexivity
                 end.
          eapply put_arg_reg; try eassumption. blia.
  Qed.

  Lemma grow_related_mem: forall maxvar frame t1 mSmall1 l1 t2 mSmall2 l2 mStack mCombined2 fpval,
      related maxvar frame fpval t1 mSmall1 l1 t2 mSmall2 l2 ->
      map.split mCombined2 mSmall2 mStack ->
      exists mCombined1, map.split mCombined1 mSmall1 mStack /\
                         related maxvar frame fpval t1 mCombined1 l1 t2 mCombined2 l2.
  Proof.
    unfold related, map.split. intros. fwd.
    eexists. ssplit. 1: reflexivity.
    { unfold sep, map.split in Hp1. fwd.
      eapply map.disjoint_putmany_l in H0p1. apply proj1 in H0p1.
      eapply map.disjoint_putmany_l in H0p1. apply proj1 in H0p1.
      assumption. }
    do 3 eexists. ssplit; try eassumption || reflexivity.
    replace (eq (map.putmany mSmall1 mStack) * word_array fpval stackwords * frame)%sep
      with (eq (map.putmany mSmall1 mStack) * (word_array fpval stackwords * frame))%sep. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    replace (eq mSmall1 * word_array fpval stackwords * frame)%sep with
        (eq mSmall1 * (word_array fpval stackwords * frame))%sep in Hp1. 2: {
     symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    forget (word_array fpval stackwords * frame)%sep as R.
    unfold sep, map.split in Hp1|-*. fwd.
    assert (map.disjoint mStack mq) as D. {
      apply map.disjoint_putmany_l in H0p1. apply proj2 in H0p1. apply map.disjoint_comm. exact H0p1.
    }
    do 2 eexists. ssplit. 4: eassumption.
    3: reflexivity.
    - rewrite <- (map.putmany_assoc mp mStack). rewrite (map.putmany_comm mStack mq) by exact D.
      rewrite map.putmany_assoc. reflexivity.
    - apply map.disjoint_putmany_l. auto.
  Qed.

  Lemma shrink_related_mem: forall maxvar frame t1 m1 l1 t2 m2 l2 mRemove m1Small fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      map.split m1 m1Small mRemove ->
      exists m2Small, map.split m2 m2Small mRemove /\
                      related maxvar frame fpval t1 m1Small l1 t2 m2Small l2.
  Proof.
    unfold related, map.split. intros. fwd.
    replace (eq (map.putmany m1Small mRemove) * word_array fpval stackwords * frame)%sep
      with (eq (map.putmany m1Small mRemove) * (word_array fpval stackwords * frame))%sep in Hp1. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    set (R := (word_array fpval stackwords * frame)%sep) in *.
    unfold sep, map.split in Hp1. fwd.
    apply map.disjoint_putmany_l in Hp1p0p1. destruct Hp1p0p1 as (D' & D).
    eexists. ssplit.
    { rewrite <- map.putmany_assoc. rewrite (map.putmany_comm mRemove mq) by exact D.
      rewrite map.putmany_assoc. reflexivity. }
    { apply map.disjoint_putmany_l. split. 1: assumption. apply map.disjoint_comm. assumption. }
    do 3 eexists. ssplit; try eassumption || reflexivity.
    replace (eq m1Small * word_array fpval stackwords * frame)%sep
      with (eq m1Small * (word_array fpval stackwords * frame))%sep. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    subst R.
    unfold sep, map.split.
    do 2 eexists. ssplit. 4: eassumption.
    1,3: reflexivity. assumption.
  Qed.

  Lemma hide_llArgRegs: forall llArgRegs R l argvals n,
      (eq llArgRegs * arg_regs * R)%sep l ->
      map.of_list_zip (List.unfoldn (Z.add 1) n a0) argvals = Some llArgRegs ->
      (n <= 8)%nat ->
      (arg_regs * R)%sep l.
  Proof.
    unfold arg_regs, sep, map.split. intros. fwd.
    exists (map.putmany mp0 mq0), mq. ssplit; auto.
    intros. rewrite map.get_putmany_dec in H. destr (map.get mq0 k); fwd; eauto.
    eapply map.of_list_zip_forall_keys in H0.
    2: eapply List.unfoldn_Z_seq_Forall.
    unfold map.forall_keys in H0. specialize H0 with (1 := H). unfold a0 in H0. blia.
  Qed.

  (* used at the beginning of a function *)
  Lemma fresh_related: forall maxvar frame fpval t m1 m2 l2 argcount vs stackwords,
      map.of_list_zip (List.firstn argcount (reg_class.all reg_class.arg)) vs = Some l2 ->
      (argcount <= 8)%nat ->
      length stackwords = Z.to_nat (maxvar - 31) ->
      (eq m1 * word_array fpval stackwords * frame)%sep m2 ->
      related maxvar frame fpval t m1 map.empty t m2 (map.put l2 fp fpval).
  Proof.
    unfold related. intros.
    eexists map.empty, map.empty, _. ssplit.
    - reflexivity.
    - eassumption.
    - intros. rewrite map.get_empty in H3. discriminate.
    - intros. rewrite map.get_empty in H3. discriminate.
    - unfold sep, map.split. exists map.empty, map.empty. rewrite map.putmany_empty_l.
      eauto using @map.disjoint_empty_r.
    - fwd. apply sep_comm. eapply sep_on_undef_put.
      + eapply map.not_in_of_list_zip_to_get_None. 1: eassumption.
        eapply not_in_arg_regs; unfold fp, RegisterNames.a0, RegisterNames.a7; blia.
      + unfold arg_regs.
        eapply map.of_list_zip_forall_keys in H. 2: {
          apply List.Forall_firstn.
          apply arg_range_Forall.
        }
        unfold map.forall_keys in *. intros. specialize H with (1 := H3). blia.
    - intros. rewrite map.get_empty in H4. discriminate.
    - assumption.
  Qed.

  Lemma arg_regs_absorbs_putmany_of_list_zip: forall n vs l l' lRegs fpval,
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      map.putmany_of_list_zip (List.firstn n (reg_class.all reg_class.arg)) vs l = Some l' ->
      (n <= 8)%nat ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l'.
  Proof.
    unfold sep, map.split, ptsto. intros.
    destruct H0 as (mp & mq & (? & ?) & (lRegs' & mA & (? & ?) & ? & ?) & ?).
    subst l lRegs' mp mq.
    pose proof H1 as PM.
    eapply map.putmany_of_list_zip_sameLength in PM.
    eapply map.sameLength_putmany_of_list with (st := mA) in PM.
    destruct PM as (mA' & PM).
    assert (arg_regs mA') as AA. {
      unfold arg_regs in *. intros. pose proof H7 as P.
      erewrite map.get_putmany_of_list_zip in H0. 2: exact PM.
      destruct_one_match_hyp. 2: eauto.
      fwd.
      eapply map.zipped_lookup_Some_in in E.
      pose proof arg_range_Forall as Q.
      eapply Forall_forall in Q. 2: eapply List.In_firstn_to_In. 2: exact E. blia.
    }
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           end.
    all: try reflexivity.
    4: exact AA.
    - apply map.map_ext. intros. erewrite map.get_putmany_of_list_zip. 2: eassumption.
      rewrite ?map.get_putmany_dec, ?map.get_put_dec, map.get_empty.
      destruct_one_match.
      + symmetry.
        pose proof E as F.
        eapply map.zipped_lookup_Some_in in E.
        pose proof arg_range_Forall as Q.
        eapply Forall_forall in Q. 2: eapply List.In_firstn_to_In. 2: exact E.
        destr (fp =? k). 1: unfold fp in *; exfalso; blia.
        erewrite map.get_putmany_of_list_zip. 2: exact PM.
        rewrite F. reflexivity.
      + destr (map.get mA' k).
        * erewrite map.get_putmany_of_list_zip in E0. 2: exact PM.
          rewrite E in E0. rewrite E0. reflexivity.
        * erewrite map.get_putmany_of_list_zip in E0. 2: exact PM.
          rewrite E in E0. rewrite E0. reflexivity.
    - unfold map.disjoint. intros * G1 G2.
      rewrite ?map.get_put_dec, ?map.get_empty in G2. fwd.
      rewrite map.get_putmany_dec in G1. destruct_one_match_hyp; fwd.
      + unfold arg_regs in AA. specialize (AA _ _ E). unfold fp in AA. blia.
      + specialize (H _ _ G1). unfold fp in H. blia.
    - unfold map.disjoint. intros * G1 G2.
      unfold arg_regs in AA.
      specialize (AA _ _ G2).
      specialize (H _ _ G1).
      unfold a0, a7 in H.
      blia.
  Qed.
  Check snext_stmt'.
  Definition spilling_correct_for(e1 e2 : env)(s1 : stmt) : Prop :=
    forall (k1 : Semantics.trace) (t1 : Semantics.io_trace) (m1 : mem) (l1 : locals) (mc1 : MetricLog)
           (post : Semantics.trace -> Semantics.io_trace -> mem -> locals -> MetricLog -> Prop),
      exec e1 s1 k1 t1 m1 l1 mc1 post ->
      forall (frame : mem -> Prop) (maxvar : Z),
        valid_vars_src maxvar s1 ->
        forall (k2 : Semantics.trace) (t2 : Semantics.io_trace) (m2 : mem) (l2 : locals) (mc2 : MetricLog) (fpval : word),
          related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
          exec e2 (spill_stmt s1) k2 t2 m2 l2 mc2
            (fun (k2' : Semantics.trace) (t2' : Semantics.io_trace) (m2' : mem) (l2' : locals) (mc2' : MetricLog) =>
               exists k1' t1' m1' l1' mc1' k1'' k2'',
                 related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\
                   post k1' t1' m1' l1' mc1' /\
                   k1' = k1'' ++ k1 /\
                   k2' = k2'' ++ k2 /\
                   forall next k10 k1''' k2''' f,
                     predicts next (k10 ++ rev k1'' ++ k1''') ->
                     predicts (fun k => f (k10 ++ rev k1'') k) k2''' ->
                     predicts (fun k => snext_stmt' e1 next (true, k10, s1, k, fpval, f)) (rev k2'' ++ k2''')).

  Definition call_spec(e: env) '(argnames, retnames, fbody)
    (k: Semantics.trace)(t: Semantics.io_trace)(m: mem)(argvals: list word)
    (post: trace -> Semantics.io_trace -> mem -> list word -> Prop): Prop :=
    forall l mc,
      map.of_list_zip argnames argvals = Some l ->
      exec e fbody k t m l mc (fun k' t' m' l' mc' =>
                                 exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                                   post k' t' m' retvals).
  
                                                                                  
  (* In exec.call, there are many maps of locals involved:

         H = High-level, L = Low-level, C = Caller, F = called Function

                   H                                       L

                  lCH1                                    lCL1
                                                   set_reg_range_to_vars
                                                          lCL2
             get/putmany_of_list                    get/putmany_of_list
                                                          lFL3
                                                   set_vars_to_reg_range
                  lFH4                                    lFL4
             function body                           function body
                  lFH5                                    lFL5
                                                   set_reg_range_to_vars
                                                          lFL6
           get/putmany_of_list                      get/putmany_of_list
                                                          lCL7
                                                   set_vars_to_reg_range
                  lCH8                                    lCL8

     To simplify, it is helpful to have a separate lemma only talking about
     what happens in the callee. TODO: actually use that lemma in case exec.call.
     Moreover, this lemma will also be used in the pipeline, where phases
     are composed based on the semantics of function calls. *)

  Lemma app_one_cons {A} (x : A) (l : list A) :
    x :: l = [x] ++ l.
  Proof. reflexivity. Qed.
  
  Lemma spill_fun_correct_aux: forall e1 e2 argnames1 retnames1 body1 argnames2 retnames2 body2,
      spill_fun (argnames1, retnames1, body1) = Success (argnames2, retnames2, body2) ->
      spilling_correct_for e1 e2 body1 ->
      forall argvals k t m (post: trace -> Semantics.io_trace -> mem -> list word -> Prop),
        call_spec e1 (argnames1, retnames1, body1) k t m argvals post ->
        call_spec e2 (argnames2, retnames2, body2) k t m argvals
          (fun k2' t' m' retvals =>
             exists k1'' k2'',
               post (k1'' ++ k) t' m' retvals /\
                 k2' = k2'' ++ k /\
                 forall next,
                   predicts next (rev k1'') ->
                   predicts (snext_fun e1 next [] (argnames1, retnames1, body1)) (rev k2'')).
  Proof.
    unfold call_spec, spilling_correct_for. intros * Sp IHexec * Ex lFL3 mc OL2.
    unfold spill_fun in Sp. fwd.
    apply_in_hyps @map.getmany_of_list_length.
    apply_in_hyps @map.putmany_of_list_zip_sameLength.
    assert (length argnames1 = length argvals) as LA. {
      rewrite List.firstn_length in *.
      change (length (reg_class.all reg_class.arg)) with 8%nat in *.
      blia.
    }
    eapply map.sameLength_putmany_of_list in LA.
    destruct LA as (lFH4 & PA).
    specialize Ex with (1 := PA). Check arg_regs_alt.
    rewrite !arg_regs_alt by blia.
    assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
      unfold bytes_per_word. destruct width_cases as [E' | E']; rewrite E'; cbv; auto.
    }
    set (maxvar' := (Z.max (max_var body1)
                           (Z.max (fold_left Z.max argnames1 0)
                                  (fold_left Z.max retnames1 0)))) in *.
    eapply exec.stackalloc. {
      rewrite Z.mul_comm.
      apply Z_mod_mult.
    }
    intros *. intros A Sp.
    destruct (anybytes_to_array_1 (mem_ok := mem_ok) _ _ _ A) as (bytes & Pt & L).
    edestruct (byte_list_to_word_list_array bytes) as (words & L' & F). {
      rewrite L.
      unfold Memory.ftprint.
      rewrite Z2Nat.id by blia.
      destr (0 <=? (maxvar' - 31)).
      - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
      - replace (Z.of_nat (Z.to_nat (maxvar' - 31))) with 0 by blia.
        rewrite Z.mul_0_r.
        apply Zmod_0_l.
    }
    eapply F in Pt. clear F.
    assert (length words = Z.to_nat (maxvar' - 31)) as L''. {
      Z.to_euclidean_division_equations; blia.
    }
    eapply exec.seq_cps.
    eapply set_vars_to_reg_range_correct.
    { eapply fresh_related with (m1 := m) (frame := eq map.empty).
      - eassumption.
      - blia.
      - exact L''.
      - rewrite sep_eq_empty_r.
        unfold sep. eauto. }
    { eassumption. }
    { eapply map.getmany_of_list_put_diff. {
        eapply List.not_In_Z_seq. unfold fp, a0. blia.
      }
      eapply map.putmany_of_list_zip_to_getmany_of_list.
      - rewrite <- arg_regs_alt by blia. exact OL2.
      - eapply List.NoDup_unfoldn_Z_seq.
    }
    { blia. }
    { reflexivity. }
    { unfold a0, a7. blia. }
    { eapply Forall_impl. 2: eapply Forall_and.
      2: eapply List.forallb_to_Forall.
      3: eassumption.
      2: {
        unfold is_valid_src_var.
        intros *. intro F.
        rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
      }
      2: eapply Forall_le_max.
      cbv beta.
      subst maxvar'. clear. blia. }
    intros tL4 mL4 lFL4 mcL4 kL4 R.
    eapply exec.seq_cps.
    eapply exec.weaken. {
      eapply IHexec. 1: apply Ex. Print related. 2: exact R.
      unfold valid_vars_src.
      eapply Forall_vars_stmt_impl.
      2: eapply max_var_sound.
      2: eapply forallb_vars_stmt_correct.
      3: eassumption.
      2: {
        unfold is_valid_src_var.
        intros *.
        rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt. reflexivity.
      }
      cbv beta. subst maxvar'. blia.
    }
    cbv beta. intros kL5 tL5 mL5 lFL5 mcL5 (kH5 & tH5 & mH5 & lFH5 & mcH5 & k1'' & k2'' & R5 & OC & Ek1'' & Ek2'' & CT).
    fwd.
    eapply set_reg_range_to_vars_correct.
    { eassumption. }
    { blia. }
    { reflexivity. }
    { unfold a0, a7. blia. }
    { eapply Forall_impl. 2: eapply Forall_and.
      2: eapply List.forallb_to_Forall.
      3: eassumption.
      2: {
        unfold is_valid_src_var.
        intros *. intro F.
        rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
      }
      2: eapply Forall_le_max.
      cbv beta.
      subst maxvar'. clear. blia. }
    { eassumption. }
    rename R into R0.
    intros tL6 lFL6 mcL6 kL6 R GM.
    (* prove that if we remove the additional stack provided by exec.stackalloc
       and store the result vars back into the arg registers, the postcondition holds *)
    unfold related in R. fwd. rename lStack into lStack5, lRegs into lRegs5.
    move A at bottom. move Sp at bottom.
    rename Rp1 into M2.
    rewrite sep_eq_empty_r in M2.
    unfold sep in M2. unfold map.split in M2.
    destruct M2 as (m2Small & mStack' & (? & ?) & ? & M2).
    subst.
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           end.
    4: { eassumption. }
    2: {
      unfold map.split. eauto.
    }
    {
      eapply cast_word_array_to_bytes in M2.
      eapply array_1_to_anybytes in M2.
      match goal with
      | H: Memory.anybytes a ?LEN1 mStack' |-
        Memory.anybytes a ?LEN2 mStack' => replace LEN2 with LEN1; [exact H|]
      end.
      erewrite List.flat_map_const_length. 2: {
        intros w. rewrite LittleEndianList.length_le_split; trivial.
      }
      blia. }
    1: eassumption.
    { subst kL6. subst kL4. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
    { intros next H.
      repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
      econstructor; eauto.
      { reflexivity. }
      cbn [snext_fun].
      apply predict_with_prefix_works.
      eapply CT.
      { simpl. instantiate (1 := nil). rewrite app_nil_r. assumption. }
      { apply predict_with_prefix_works_end. constructor. reflexivity. } }
     Unshelve.
    all: try assumption.
  Qed.

  Lemma predict_with_prefix_works_weirdly'
     : forall (prefix : trace) (predict_rest : trace -> trace -> option qevent) (rest : trace),
       (forall t1 t2, rest = t1 ++ t2 -> predicts (predict_rest (prefix ++ t1)) rest) ->
       predicts (fun t => predict_with_prefix prefix (predict_rest t) t) (prefix ++ rest).
  Proof.
    clear. intros. Admitted. (*induction prefix.
    - simpl in *. admit.
    - simpl. econstructor; [reflexivity|reflexivity|]. apply IHprefix.

   induction rest. a
      + sprewrite app_nil_r in *. simpl. specialize (H nil nil eq_refl). rewrite app_nil_r in H.
      Check predict_with_prefix_works.
      admit.
    - Print Semantics.predicts.
      induction prefix.
      + simpl. constructor. inversion H. assumption.
      + simpl. econstructor; [reflexivity|reflexivity|]. simpl. simpl in H.
  Admitted. Check Semantics.predict_with_prefix_works_eq.*)

  Lemma predict_with_prefix_works_weirdly
     : forall (prefix : trace) (predict_rest : trace -> trace -> option qevent) (rest : trace),
       (forall t, (length prefix <= length t)%nat -> predicts (predict_rest t) rest) ->
       predicts (fun t => predict_with_prefix prefix (predict_rest t) t) (prefix ++ rest).
  Proof. Admitted. Check Semantics.predict_with_prefix_works_eq.

  Lemma predict_with_prefix_works_weirdly_eq
    : forall stuff prefix rest predict_rest,
      stuff = prefix ++ rest ->
      (forall t, (length prefix <= length t)%nat -> predicts (predict_rest t) rest) ->
      predicts (fun t => predict_with_prefix prefix (predict_rest t) t) stuff.
  Proof. Admitted.
  
  Lemma spilling_correct : forall
      (e1 e2 : env)
      (Ev : spill_functions e1 = Success e2)
      (s1 : stmt)
      (k1 : Semantics.trace)
      (t1 : Semantics.io_trace)
      (m1 : mem)
      (l1 : locals)
      (mc1 : MetricLog)
      (post : Semantics.trace -> Semantics.io_trace -> mem -> locals -> MetricLog -> Prop),
      exec e1 s1 k1 t1 m1 l1 mc1 post ->
      forall (frame : mem -> Prop) (maxvar : Z),
        valid_vars_src maxvar s1 ->
        forall (k2 : Semantics.trace) (t2 : Semantics.io_trace) (m2 : mem) (l2 : locals) (mc2 : MetricLog) (fpval : word),
          related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
          exec e2 (spill_stmt s1) k2 t2 m2 l2 mc2
            (fun (k2' : Semantics.trace) (t2' : Semantics.io_trace) (m2' : mem) (l2' : locals) (mc2' : MetricLog) =>
               exists k1' t1' m1' l1' mc1' k1'' k2'',
                 related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\
                   post k1' t1' m1' l1' mc1' /\
                   k1' = k1'' ++ k1 /\
                   k2' = k2'' ++ k2 /\
                   forall next k10 k1''' k2''' f,
                     predicts next (k10 ++ rev k1'' ++ k1''') ->
                     predicts (fun k => f (k10 ++ rev k1'') k) k2''' ->
                     predicts (fun k => snext_stmt' e1 next (true, k, s1, k10, fpval, f)) (rev k2'' ++ k2''')).
  Proof.
    intros e1 e2 Ev. intros s1 k1 t1 m1 l1 mc1 post.
    induction 1; intros; cbn [spill_stmt valid_vars_src Forall_vars_stmt] in *; fwd.
    - (* exec.interact *)
      eapply exec.seq_cps.
      eapply set_reg_range_to_vars_correct; try eassumption; try (unfold a0, a7; blia).
      intros *. intros R GM. clear l2 mc2 H4.
      unfold related in R. fwd.
      spec (subst_split (ok := mem_ok) m) as A.
      1: eassumption. 1: ecancel_assumption.
      edestruct (@sep_def _ _ _ m2 (eq mGive)) as (mGive' & mKeepL & B & ? & C).
      1: ecancel_assumption.
      subst mGive'.
      eapply exec.seq_cps.
      eapply @exec.interact with (mGive := mGive).
      + eapply map.split_comm. exact B.
      + rewrite arg_regs_alt by blia. 1: eassumption.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        fwd.
        rename l into l1, l' into l1'.
        rename H2p0 into Q.
        assert (List.length (List.firstn (length resvars) (reg_class.all reg_class.arg)) =
                List.length resvals) as HL. {
          eapply map.putmany_of_list_zip_sameLength in Q. rewrite <- Q.
          rewrite List.firstn_length. change (length (reg_class.all reg_class.arg)) with 8%nat.
          blia.
        }
        eapply map.sameLength_putmany_of_list in HL. destruct HL as (l2'' & ER).
        eexists. split. 1: exact ER.
        intros.
        eapply set_vars_to_reg_range_correct; cycle 1.
        { eassumption. }
        { eapply map.putmany_of_list_zip_to_getmany_of_list.
          - rewrite <- arg_regs_alt by blia. eassumption.
          - eapply List.NoDup_unfoldn_Z_seq. }
        { blia. }
        { reflexivity. }
        { unfold a0, a7. blia. }
        { eassumption. }
        { intros. do 7 eexists.
          split. 1: eassumption.
          eenough _ as Hpost.
          2: { eapply H2p1.
               unfold map.split. split; [reflexivity|].
               move C at bottom.
               unfold sep at 1 in C. destruct C as (mKeepL' & mRest & SC & ? & _). subst mKeepL'.
               move H2 at bottom. unfold map.split in H2. fwd.
               eapply map.shrink_disjoint_l; eassumption. }
          clear H2p1.
          split. 1: eassumption.
          split.
          { instantiate (1 := [_]). reflexivity. }
          split.
          { subst k2'0 k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
          (*begin ct stuff for interact*)
          intros.
          repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
          eapply Semantics.predicts_ext.
          2: { intros k0. Check snext_stmt'_step. symmetry. rewrite snext_stmt'_step.
               simpl. reflexivity. }
          apply Semantics.predict_cons in H5. rewrite H5. simpl.
          apply predict_with_prefix_works. apply H6.
          (*end ct stuff for interact*)
        }
        (* related for set_vars_to_reg_range_correct: *)
        unfold related.
        eexists _, _, _. ssplit.
        * reflexivity.
        * eenough ((eq _ * (word_array fpval stackwords * frame))%sep m') as En.
          1: ecancel_assumption.
          move C at bottom.
          eapply grow_eq_sep. 1: exact C. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eapply arg_regs_absorbs_putmany_of_list_zip; try eassumption.
        * eassumption.
        * eassumption.
    - (* exec.call *)
      (* H = High-level, L = Low-level, C = Caller, F = called Function

                   H                                       L

                  lCH1                                    lCL1
                                                   set_reg_range_to_vars
                                                          lCL2
             get/putmany_of_list                    get/putmany_of_list
                                                          lFL3
                                                   set_vars_to_reg_range
                  lFH4                                    lFL4
             function body                           function body
                  lFH5                                    lFL5
                                                   set_reg_range_to_vars
                                                          lFL6
           get/putmany_of_list                      get/putmany_of_list
                                                          lCL7
                                                   set_vars_to_reg_range
                  lCH8                                    lCL8
      *)
      rename l into lCH1, l2 into lCL1, st0 into lFH4.
      rename H4p0 into FR, H4p1 into FA.
      unfold spill_functions in Ev.
      eapply map.try_map_values_fw in Ev. 2: eassumption.
      unfold spill_fun in Ev. fwd.
      eapply exec.seq_cps.
      apply_in_hyps @map.getmany_of_list_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      eapply set_reg_range_to_vars_correct; try eassumption || (unfold a0, a7 in *; blia).
      intros ? lCL2 ? ? ? ?.
      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
        unfold bytes_per_word. destruct width_cases as [E' | E']; rewrite E'; cbv; auto.
      }
      eapply exec.seq_cps.
      assert (length (List.firstn (length params) (reg_class.all reg_class.arg)) = length argvs)
        as L. {
        rewrite List.firstn_length. change (length (reg_class.all reg_class.arg)) with 8%nat. blia.
      }
      eapply map.sameLength_putmany_of_list in L.
      destruct L as (lFL3 & P).
      rewrite !arg_regs_alt by blia.
      eapply exec.call_cps; try eassumption.
      set (maxvar' := (Z.max (max_var fbody)
                             (Z.max (fold_left Z.max params 0) (fold_left Z.max rets 0)))) in *.
      eapply exec.stackalloc. {
        rewrite Z.mul_comm.
        apply Z_mod_mult.
      }
      intros *. intros A Sp.
      destruct (anybytes_to_array_1 (mem_ok := mem_ok) _ _ _ A) as (bytes & Pt & L).
      edestruct (byte_list_to_word_list_array bytes) as (words & L' & F). {
        rewrite L.
        unfold Memory.ftprint.
        rewrite Z2Nat.id by blia.
        destr (0 <=? (maxvar' - 31)).
        - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
        - replace (Z.of_nat (Z.to_nat (maxvar' - 31))) with 0 by blia.
          rewrite Z.mul_0_r.
          apply Zmod_0_l.
      }
      eapply F in Pt. clear F.
      assert (length words = Z.to_nat (maxvar' - 31)) as L''. {
        Z.to_euclidean_division_equations; blia.
      }
      eapply exec.seq_cps.
      unfold related in H4. fwd. rename lStack into lStack1, lRegs into lRegs1.
      eapply set_vars_to_reg_range_correct.
      { eapply fresh_related with (m1 := m) (frame := (word_array fpval stackwords * frame)%sep).
        - eassumption.
        - blia.
        - exact L''.
        - enough ((eq m * word_array fpval stackwords * frame * word_array a words)%sep mCombined).
          1: ecancel_assumption.
          unfold sep at 1. do 2 eexists.
          split. 1: exact Sp.
          split. 1: ecancel_assumption. exact Pt. }
      { eassumption. }
      { eapply map.getmany_of_list_put_diff. {
          eapply List.not_In_Z_seq. unfold fp, a0. blia.
        }
        eapply map.putmany_of_list_zip_to_getmany_of_list.
        - rewrite <- arg_regs_alt by blia. exact P.
        - eapply List.NoDup_unfoldn_Z_seq.
      }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eapply Forall_impl. 2: eapply Forall_and.
        2: eapply List.forallb_to_Forall.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *. intro F.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
        }
        2: eapply Forall_le_max.
        cbv beta.
        subst maxvar'. clear. blia. }
      intros tL4 mL4 lFL4 mcL4 kL4 R.
      eapply exec.seq_cps.
      eapply exec.weaken. {
        eapply IHexec.
        2: exact R.
        unfold valid_vars_src.
        eapply Forall_vars_stmt_impl.
        2: eapply max_var_sound.
        2: eapply forallb_vars_stmt_correct.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt. reflexivity.
        }
        cbv beta. subst maxvar'. blia.
      }
      cbv beta. intros kL5 tL5 mL5 lFL5 mcL5 (kH5 & tH5 & mH5 & lFH5 & mcH5 & kH5' & tH5' & tL5' & R5 & OC & EkL5 & CT).
      match goal with
      | H: context[outcome], A: context[outcome] |- _ =>
        specialize H with (1 := A); move H at bottom; rename H into Q
      end.
      fwd. rename l' into lCH8.
      eapply set_reg_range_to_vars_correct.
      { eassumption. }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eapply Forall_impl. 2: eapply Forall_and.
        2: eapply List.forallb_to_Forall.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *. intro FF.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in FF. exact FF.
        }
        2: eapply Forall_le_max.
        cbv beta.
        subst maxvar'. clear. blia. }
      { eassumption. }
      rename R into R0.
      intros tL6 lFL6 mcL6 kL6 R GM.
      (* prove that if we remove the additional stack provided by exec.stackalloc
         and store the result vars back into the caller's registers,
         states are still related and postcondition holds *)
      unfold related in R. fwd. rename lStack into lStack5, lRegs into lRegs5.
      move A at bottom. move Sp at bottom.
      assert ((eq mH5 * word_array fpval stackwords * frame * word_array a stackwords0)%sep mL5)
        as M2 by ecancel_assumption.
      unfold sep in M2 at 1. unfold map.split in M2.
      destruct M2 as (m2Small & mStack' & (? & ?) & ? & M2).
      assert (length (List.unfoldn (BinInt.Z.add 1) (length binds) a0) = length retvs) as PM67. {
        apply_in_hyps @map.getmany_of_list_length.
        apply_in_hyps @map.putmany_of_list_zip_sameLength.
        congruence.
      }
      eapply map.sameLength_putmany_of_list with (st := lCL2) in PM67.
      destruct PM67 as (lCL7 & PM67).
      subst mL5. unfold map.split.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      2: reflexivity.
      {
        eapply cast_word_array_to_bytes in M2.
        eapply array_1_to_anybytes in M2.
        match goal with
        | H: Memory.anybytes a ?LEN1 mStack' |-
          Memory.anybytes a ?LEN2 mStack' => replace LEN2 with LEN1; [exact H|]
        end.
        erewrite List.flat_map_const_length. 2: {
          intros w. rewrite LittleEndianList.length_le_split; trivial.
        }
        simpl. blia. }
      { eassumption. }
      { rewrite arg_regs_alt by blia. eassumption. }
      { exact PM67. }
      eapply set_vars_to_reg_range_correct.
      { unfold related. eexists lStack1, lRegs1, _. ssplit.
        { reflexivity. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eapply arg_regs_absorbs_putmany_of_list_zip; try eassumption.
          apply_in_hyps @map.getmany_of_list_length.
          apply_in_hyps @map.putmany_of_list_zip_sameLength.
          replace (length rets) with (length binds) by congruence.
          rewrite arg_regs_alt by blia. exact PM67. }
        { eassumption. }
        { eassumption. }
      }
      { eassumption. }
      { eapply map.putmany_of_list_zip_to_getmany_of_list. 1: exact PM67.
        eapply List.NoDup_unfoldn_Z_seq. }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eassumption. }
      { intros t22 m22 l22 mc22 k22 R22. do 7 eexists. split; [eassumption|].
        split; [eassumption|].
        (* begin ct stuff for call*)
        split.
        { subst kH5. rewrite app_one_cons. rewrite app_assoc. reflexivity. }
        split.
        { subst k22. subst kL6. subst kL5. subst kL4. subst k2'.
          rewrite app_one_cons. rewrite (app_one_cons leak_unit). repeat rewrite app_assoc.
          reflexivity. }
        intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        eapply Semantics.predicts_ext.
        2: { intros. symmetry. rewrite snext_stmt'_step. simpl. reflexivity. }
        rewrite H. 
        rewrite rev_app_distr in H3. repeat rewrite <- app_assoc in H3. assert (H3' := H3).
        Print Semantics.predict_with_prefix.
        pop_k_elts 
        eapply predict_with_prefix_works_weirdly_eq.
        { repeat rewrite <- app_assoc. simpl. reflexivity. }
        intros.
        simpl. econstructor.
        { reflexivity. }
        { eauto. }
        { eapply predict_with_prefix_works_weirdly_eq.
          { repeat rewrite <- app_assoc. simpl. reflexivity. }
          intros. Check predict_with_prefix_works_weirdly.
          (*should copy what I did in flattoriscv so i don't have to deal with this associativity 
            nonsense.*)
          repeat rewrite <- app_assoc. apply predict_with_prefix_works.
          eapply CT.
          { repeat rewrite <- app_assoc. eassumption. }
          { rewrite app_assoc. apply predict_with_prefix_works.
            rewrite <- app_assoc. rewrite rev_app_distr in H8. apply H8. }
          { blia. }
        (* end ct stuff for call*)
      } }

    - (* exec.load *)
      eapply exec.seq_cps.
      eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      eapply exec.seq_cps.
      pose proof H2 as A. unfold related in A. fwd.
      unfold Memory.load, Memory.load_Z, Memory.load_bytes in *. fwd.
      eapply exec.load. {
        rewrite map.get_put_same. reflexivity. }
      { edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
        1: ecancel_assumption. unfold map.split in Sp. subst. fwd.
        unfold Memory.load, Memory.load_Z, Memory.load_bytes.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      eapply save_ires_reg_correct''.
      + eassumption.
      + blia.
      + (*begin ct stuff for load*)
        intros. do 7 eexists. split; [|split]. 2: eassumption. 1: eassumption.
        split.
        { rewrite app_one_cons. reflexivity. }
        split.
        { subst k2'0. subst k2'. rewrite app_one_cons. repeat rewrite app_assoc.
          reflexivity. }
        intros. exists (S O). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl. 
        simpl in H3. apply Semantics.predict_cons in H3. rewrite H3. simpl.
        apply predict_with_prefix_works. assumption.
    (*end ct stuff for load*)
        
    - (* exec.store *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H4. intros.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      pose proof H3 as A. unfold related in A. fwd.
      unfold Memory.store, Memory.store_Z, Memory.store_bytes in *. fwd.
      edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
      1: ecancel_assumption. unfold map.split in Sp. subst. fwd.
      eapply exec.store.
      1: eapply get_iarg_reg_1; eauto with zarith.
      1: apply map.get_put_same.
      { unfold Memory.store, Memory.store_Z, Memory.store_bytes.
        unfold Memory.load_bytes in *.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      do 7 eexists. split; [|split]. 2: eassumption.
      { unfold related.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        all: try eassumption || reflexivity.
        spec store_bytes_sep_hi2lo as A. 1: eassumption.
        all: ecancel_assumption. }
      (*begin ct stuff for store*)
      split.
      { subst k2'0. subst k2'. rewrite app_one_cons. repeat rewrite app_assoc.
        reflexivity. }
      split.
      { subst k2'0. subst k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
      intros. exists (S O). intros.
      repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
      destruct fuel' as [|fuel']; [blia|]. simpl. 
      simpl in H1. apply Semantics.predict_cons in H1. rewrite H1. simpl.
      apply predict_with_prefix_works. assumption.
      (*end ct stuff for store*)
    - (* exec.inlinetable *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H4. intros.
      eapply exec.seq_cps.
      eapply exec.inlinetable.
      { unfold ires_reg, iarg_reg, spill_tmp, fp, a0, a7 in *. destr (32 <=? x); destr (32 <=? i); try blia. }
      { rewrite map.get_put_same. reflexivity. }
      { eassumption. }
      eapply save_ires_reg_correct''.
      + eassumption.
      + blia.
      + intros. do 7 eexists. split; [|split].
        2: eassumption. 1: assumption. split.
        { instantiate (1 := [_]). reflexivity. } split.
        { subst k2'0 k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
        intros. exists (S O). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl.
        apply Semantics.predict_cons in H5. rewrite H5.
        apply predict_with_prefix_works. assumption.
    - (* exec.stackalloc *)
      rename H1 into IH.
      eapply exec.stackalloc. 1: assumption.
      intros.
      eapply exec.seq_cps.
      edestruct grow_related_mem as (mCombined1 & ? & ?). 1,2: eassumption.
      eapply save_ires_reg_correct''. 1: eassumption. 1: blia.
      intros.
      eapply exec.weaken. {
        eapply IH; eassumption. }
      cbv beta. intros. fwd.
      edestruct shrink_related_mem as (mSmall2 & ? & ?). 1,2: eassumption.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1,2,3,4: eassumption.
      { rewrite app_one_cons. rewrite app_assoc. reflexivity. }
      { subst k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
      intros. rename H7p4 into CT. intros.
      repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
      Unshelve. 2: apply (S F').
      destruct fuel' as [|fuel']; [blia|]. simpl. econstructor; auto.
      rewrite <- app_assoc. apply predict_with_prefix_works.
      rewrite rev_app_distr in H9, H10. simpl in H9, H10.
      eapply CT.
      { intros. rewrite <- app_assoc. simpl. eassumption. }
      { rewrite <- app_assoc. simpl. eassumption. }
      { blia. }
    (*end ct stuff for stackalloc*) 
    - (* exec.lit *)
      eapply exec.seq_cps. eapply exec.lit.
      eapply save_ires_reg_correct''.
      { eassumption. }
      { blia. }
      intros. do 7 eexists. split; [eassumption|]. split; [eassumption|]. split.
      { instantiate (1 := nil). reflexivity. } split.
      { subst k2'. reflexivity. }
      intros. exists (S O). intros.
      repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
      destruct fuel' as [|fuel']; [blia|]. simpl. 
      apply predict_with_prefix_works. rewrite app_nil_r in H3. assumption.
      (*end ct stuff for lit*)
    - (* exec.op *)
      unfold exec.lookup_op_locals in *.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros. destruct_one_match; fwd.
      {
        eapply exec.seq_cps. eapply exec.seq_cps.  eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.op.
        { eapply get_iarg_reg_1; eauto with zarith. }
        { unfold exec.lookup_op_locals in *. apply map.get_put_same. }
        eapply save_ires_reg_correct''; try (eassumption || blia).
        (*begin ct stuff for op*)
        intros. do 7 eexists. split; [eassumption|]. split; [eassumption|]. split.
        { reflexivity. } split.
        { subst k2'1 k2'0 k2'. repeat rewrite app_assoc. reflexivity. }
        intros. exists (S O). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl.
        destruct op.
        all: try (apply predict_with_prefix_works; assumption).
        all: try (apply Semantics.predict_cons in H4; rewrite H4; simpl;
                  apply predict_with_prefix_works; assumption).
        { assert (H4' := H4). apply Semantics.predict_cons in H4. rewrite H4. simpl.
          simpl in H4'. rewrite app_one_cons, app_assoc in H4'.
          apply Semantics.predict_cons in H4'. rewrite H4'. simpl.
          apply predict_with_prefix_works; assumption. }
        { assert (H4' := H4). apply Semantics.predict_cons in H4. rewrite H4. simpl.
          simpl in H4'. rewrite app_one_cons, app_assoc in H4'.
          apply Semantics.predict_cons in H4'. rewrite H4'. simpl.
          apply predict_with_prefix_works; assumption. }
      (*end ct stuff for op*)
      }
      {
        eapply exec.seq_cps. eapply exec.op.
        { apply map.get_put_same. }
        { unfold exec.lookup_op_locals in *. reflexivity. }
        eapply save_ires_reg_correct''; try (eassumption || blia).
        (*begin ct stuff for op*)
        intros. do 7 eexists. split; [eassumption|]. split; [eassumption|]. split.
        { reflexivity. } split.
        { subst k2'0 k2'. repeat rewrite app_assoc. reflexivity. }
        intros. exists (S O). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl.
        destruct op.
        all: try (apply predict_with_prefix_works; assumption).
        all: try (apply Semantics.predict_cons in H3; rewrite H3; simpl;
                  apply predict_with_prefix_works; assumption).
        { assert (H3' := H3). apply Semantics.predict_cons in H3. rewrite H3. simpl.
          simpl in H3'. rewrite app_one_cons, app_assoc in H3'.
          apply Semantics.predict_cons in H3'. rewrite H3'. simpl.
          apply predict_with_prefix_works; assumption. }
        { assert (H3' := H3). apply Semantics.predict_cons in H3. rewrite H3. simpl.
          simpl in H3'. rewrite app_one_cons, app_assoc in H3'.
          apply Semantics.predict_cons in H3'. rewrite H3'. simpl.
          apply predict_with_prefix_works; assumption. }
      (*end ct stuff for op*)
      }
    - (* exec.set *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H2. intros.
      eapply exec.seq_cps.
      eapply exec.set. 1: apply map.get_put_same.
      eapply save_ires_reg_correct''; [eassumption|blia|].
      intros. do 7 eexists. split; [eassumption|]. split; [eassumption|]. split.
      { instantiate (1 := nil). reflexivity. } split.
      { subst k2'0 k2'. repeat rewrite app_assoc. reflexivity. }
      intros. exists (S O). intros.
      repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
      destruct fuel' as [|fuel']; [blia|]. simpl. 
      apply predict_with_prefix_works. rewrite app_nil_r in H4. assumption.
    - (* exec.if_true *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2. intros.
        eapply exec.if_true. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply exec.weaken.
        { eapply IHexec; eassumption. }
        cbv beta. intros k' t' m' l' mc' (k1' & t1' & m1' & l1' & mc1' & k1'' & k2'' & R & Hpost & Ek1'' & Ek2'' & CT). subst.
        do 7 eexists.
        split; [eassumption|]. split; [eassumption|]. split.
        { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
        { subst k2'0 k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
        destruct CT as [F' CT]. exists (S F'). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl. 
        rewrite rev_app_distr in H3, H4. simpl in H3.
        assert (H3' := Semantics.predict_cons _ _ _ _ H3). rewrite H3'. simpl.
        rewrite (app_one_cons _ (rev k2'')).
        repeat rewrite app_assoc. rewrite <- (app_assoc _ _ k2''').
        apply predict_with_prefix_works. clear IHexec.
        eapply CT.
        { rewrite <- app_assoc. simpl. eassumption. }
        { rewrite <- app_assoc. simpl. eassumption. }
        { blia. }
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_true. {
          cbn. rewrite map.get_put_same. rewrite word.eqb_ne by assumption. reflexivity.
        }
        eapply exec.weaken.
        { eapply IHexec; eassumption. }
        cbv beta. intros k' t' m' l' mc' (k1' & t1' & m1' & l1' & mc1' & t1'' & t2'' & R & Hpost & Ek1'' & Ek2'' & CT). subst.
        do 7 eexists.
        split; [eassumption|]. split; [eassumption|]. split.
        { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
        { subst k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
        destruct CT as [F' CT]. exists (S F'). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl. 
        rewrite rev_app_distr in H2, H3. simpl in H2.
        assert (H2' := Semantics.predict_cons _ _ _ _ H2). rewrite H2'. simpl.
        rewrite (app_one_cons _ (rev t2'')).
        repeat rewrite app_assoc. rewrite <- (app_assoc _ _ k2''').
        apply predict_with_prefix_works. clear IHexec. Search snext_stmt'. Search t2''.
        eapply CT.
        { rewrite <- app_assoc. simpl. eassumption. }
        { rewrite <- app_assoc. simpl. eassumption. }
        { blia. }
    - unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2. intros.
        eapply exec.if_false. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply exec.weaken.
        { apply IHexec; eassumption. }
        cbv beta. intros k' t' m' l' mc' (k1' & t1' & m1' & l1' & mc1' & k1'' & k2'' & R & Hpost & Ek1'' & Ek2'' & CT). subst.
        do 7 eexists.
        split; [eassumption|]. split; [eassumption|]. split.
        { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
        { subst k2'0 k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
        destruct CT as [F' CT]. exists (S F'). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl. 
        rewrite rev_app_distr in H3, H4. simpl in H3.
        assert (H3' := Semantics.predict_cons _ _ _ _ H3). rewrite H3'. simpl.
        rewrite (app_one_cons _ (rev k2'')).
        repeat rewrite app_assoc. rewrite <- (app_assoc _ _ k2''').
        apply predict_with_prefix_works. clear IHexec.
        eapply CT.
        { rewrite <- app_assoc. simpl. eassumption. }
        { rewrite <- app_assoc. simpl. eassumption. }
        { blia. }
        
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_false. {
          cbn. rewrite map.get_put_same. rewrite word.eqb_eq; reflexivity.
        }
        eapply exec.weaken.
        { apply IHexec; eassumption. }
        cbv beta. intros k' t' m' l' mc' (k1' & t1' & m1' & l1' & mc1' & t1'' & t2'' & R & Hpost & Ek1'' & Ek2'' & CT). subst.
        do 7 eexists.
        split; [eassumption|]. split; [eassumption|]. split.
        { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
        { subst k2'. rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
        destruct CT as [F' CT]. exists (S F'). intros.
        repeat (rewrite rev_app_distr || rewrite rev_involutive || cbn [rev List.app]).
        destruct fuel' as [|fuel']; [blia|]. simpl. 
        rewrite rev_app_distr in H1, H2. simpl in H1.
        assert (H1' := Semantics.predict_cons _ _ _ _ H1). rewrite H1'. simpl.
        rewrite (app_one_cons _ (rev t2'')).
        repeat rewrite app_assoc. rewrite <- (app_assoc _ _ k2''').
        apply predict_with_prefix_works. clear IHexec. Search snext_stmt'. Search t2''.
        eapply CT.
        { rewrite <- app_assoc. simpl. eassumption. }
        { rewrite <- app_assoc. simpl. eassumption. }
        { blia. }
    - (* exec.loop *)
      rename IHexec into IH1, H3 into IH2, H5 into IH12.
      eapply exec.loop_cps.
      eapply exec.seq.
      1: eapply IH1; eassumption.
      cbv beta. intros. fwd.
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond] in *; fwd.
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.seq. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        erewrite get_iarg_reg_1 by eauto with zarith.
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 7 eexists. split; [|split].
          2: { Search post. eapply H1. 1: eassumption. cbn. rewrite E, E0. congruence. }
          { eassumption. } split.
          { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
          { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
          exists (S F'). intros. destruct fuel' as [|fuel']; [blia|]. simpl.
          repeat (rewrite rev_involutive || rewrite rev_app_distr || rewrite <- app_assoc).
          simpl in H5, H6. rewrite <- app_assoc in H5. eapply H3p4. 
          { apply H5. }
          { rewrite (app_assoc k10) in H5. apply Semantics.predict_cons in H5. rewrite H5. simpl.
            rewrite (app_one_cons _ k2'''). repeat rewrite (app_assoc _ _ k2''').
            apply predict_with_prefix_works. rewrite <- app_assoc. assumption. }
          { blia. }
        * Check exec.loop_cps. eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E, E0. Search r0. congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. fwd. eapply exec.weaken.
             ++ eapply IH12; eauto 10.
             ++ cbv beta. intros.
                destruct H5 as [k1' [t1'1 [m1'1 [l1'1 [mc1'1 [t1''1 [t2''1 [R [Hpost [E1 [E2 [F'1 CT]]]]]]]]]]]].
                subst. do 7 eexists.
                split; [eassumption|]. split; [eassumption|]. split.
                { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. } split. 
                { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
                exists (S (plus F'0 (plus F' F'1))). intros.
                repeat (rewrite rev_involutive || rewrite rev_app_distr || rewrite <- app_assoc).
                destruct fuel' as [|fuel']; [blia|]. simpl.
                repeat (rewrite rev_involutive in H5 || rewrite rev_app_distr in H5 || rewrite <- app_assoc in H5). Search body1.
                eapply H3p4.
                { eassumption. }
                { rewrite (app_assoc k10) in H5.
                  assert (H5' := Semantics.predict_cons _ _ _ _ H5). rewrite H5'. simpl.
                  rewrite (app_one_cons _ (_ ++ _)).
                  repeat rewrite app_assoc. repeat rewrite <- (app_assoc ((_ ++ _) ++ _)).
                  apply predict_with_prefix_works. Search body2. eapply H5p4.
                  { repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H5. eassumption. }
                  { repeat (rewrite rev_involutive in * || rewrite rev_app_distr in * || rewrite <- app_assoc in * ).
                    eapply CT.
                    { repeat rewrite <- app_assoc. eassumption. }
                    { repeat rewrite <- app_assoc. eassumption. }
                    blia. }
                  blia. }
                blia.
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 7 eexists. split; [|split].
          2: { eapply H1. 1: eassumption. cbn. rewrite E. congruence. }
          { simpl. eassumption. } split.
          { rewrite app_one_cons. rewrite app_assoc. reflexivity. } split.
          { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
          exists (S F'). intros. destruct fuel' as [|fuel']; [blia|]. simpl.
          repeat (rewrite rev_involutive || rewrite rev_app_distr || rewrite <- app_assoc).
          Search body1. eapply H3p4.
          { rewrite rev_app_distr in H5. repeat rewrite <- app_assoc in H5. eassumption. }
          { rewrite rev_app_distr in H5. repeat rewrite <- app_assoc in H5. simpl in H5.
            rewrite app_assoc in H5.
            assert (H5' := Semantics.predict_cons _ _ _ _ H5). rewrite H5'. simpl.
            rewrite (app_one_cons _ k2'''). rewrite (app_assoc _ _ k2''').
            apply predict_with_prefix_works. simpl in H6. repeat rewrite <- app_assoc.
            eassumption. }
          blia.
        * eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E. congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. fwd. eapply exec.weaken.
             ++ eapply IH12; eauto 10.
             ++ cbv beta. intros.
                destruct H5 as [k1' [t1'1 [m1'1 [l1'1 [mc1'1 [t1''1 [t2''1 [R [Hpost [E1 [E2 [F'1 CT]]]]]]]]]]]].
                subst. do 7 eexists.
                split; [eassumption|]. split; [eassumption|]. split.
                { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. } split. 
                { rewrite app_one_cons. repeat rewrite app_assoc. reflexivity. }
                exists (S (plus F'0 (plus F' F'1))). intros.
                repeat (rewrite rev_involutive || rewrite rev_app_distr || rewrite <- app_assoc).
                destruct fuel' as [|fuel']; [blia|]. simpl.
                repeat (rewrite rev_involutive in H5 || rewrite rev_app_distr in H5 || rewrite <- app_assoc in H5). Search body1.
                eapply H3p4.
                { eassumption. }
                { rewrite (app_assoc k10) in H5.
                  assert (H5' := Semantics.predict_cons _ _ _ _ H5). rewrite H5'. simpl.
                  rewrite (app_one_cons _ (_ ++ _)).
                  repeat rewrite app_assoc. rewrite <- (app_assoc ((_ ++ _) ++ _)). rewrite <- (app_assoc ((_ ++ _))).
                  apply predict_with_prefix_works. Search body2. eapply H5p4.
                  { repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H5. eassumption. }
                  { repeat (rewrite rev_involutive in * || rewrite rev_app_distr in * || rewrite <- app_assoc in * ).
                    eapply CT.
                    { repeat rewrite <- app_assoc. eassumption. }
                    { repeat rewrite <- app_assoc. eassumption. }
                    blia. }
                  blia. }
                blia.        
    - (* exec.seq *)
      cbn in *. fwd.
      rename H1 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption. eauto 15.
      + cbn. intros. fwd. eapply exec.weaken.
        -- eapply IH2; eauto.
        -- cbv beta. intros. destruct H1 as [k1' [t1'1 [m1'1 [l1'1 [mc1'1 [t1''1 [t2''1 [R [Hpost [E1 [E2 [F'1 CT]]]]]]]]]]]]. subst.
           do 7 eexists. split; [eassumption|]. split; [eassumption|]. split.
           { rewrite app_assoc. reflexivity. } split.
           { rewrite app_assoc. reflexivity. }
           exists (S (plus F' F'1)).
           intros. destruct fuel' as [|fuel']; [blia|].
           simpl. rewrite rev_app_distr. rewrite <- app_assoc. eapply H1p4.
           { rewrite rev_app_distr in H1. repeat rewrite <- app_assoc in H1. eassumption. }
           { eapply CT.
             { rewrite rev_app_distr in H1. repeat rewrite <- app_assoc in *. eassumption. }
             { repeat rewrite <- app_assoc. rewrite rev_app_distr in H2. eassumption. }
             blia. }
           blia.
    - (* exec.skip *)
      eapply exec.skip. do 7 eexists. repeat (split; [eauto|]). 1: instantiate (1 := nil).
      2: instantiate (1 := nil). all: eauto. exists (S O). intros.
      destruct fuel' as [|fuel']; [blia|]. simpl. simpl in H2.
      rewrite app_nil_r in H2. eassumption.
  Qed.

  Lemma spill_fun_correct: forall e1 e2 argnames1 retnames1 body1 argnames2 retnames2 body2,
      spill_functions e1 = Success e2 ->
      spill_fun (argnames1, retnames1, body1) = Success (argnames2, retnames2, body2) ->
      forall argvals k t m (post: Semantics.trace -> Semantics.io_trace -> mem -> list word -> Prop),
        call_spec e1 (argnames1, retnames1, body1) k t m argvals post ->
        call_spec e2 (argnames2, retnames2, body2) k t m argvals
          (fun k2' t' m' retvals =>
             exists k1'' k2'',
               post (k1'' ++ k) t' m' retvals /\
                 k2' = k2'' ++ k /\
                 exists F,
                 forall fuel,
                   (F <= fuel)%nat ->
                   forall next,                   
                     predicts next (rev k1'') ->
                     predicts (snext_fun e1 fuel next [] (argnames1, retnames1, body1)) (rev k2'')).
  Proof.
    intros. eapply spill_fun_correct_aux; try eassumption.
    unfold spilling_correct_for.
    eapply spilling_correct.
    assumption.
  Qed.

End Spilling.
