(*almost copied verbatim from the standard library*)
(*allows for general recursion where one argument to recursive function is a function, without using funext axiom *)
Section FixPoint.

Variable A : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable P : Type. (* really I want to say that P gives one type for each equivalence class
                      of A wrt the equivalence relation E.  Not clear how to say this though.*)
Variable F : forall x:A, (forall y:A, R y x -> P) -> P.
Variable E1 : A -> A -> Prop.
Variable E2 : P -> P -> Prop.

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
    E1 x1 x2 ->
    (forall (y1 y2:A) (p1:R y1 x1) (p2:R y2 x2),
        E1 y1 y2 -> E2 (f1 y1 p1) (f2 y2 p2)) -> E2 (F x1 f1) (F x2 f2).

Lemma my_Fix_F_inv : forall (x1 x2:A) (r1:Acc R x1) (r2:Acc R x2),
    E1 x1 x2 -> E2 (my_Fix_F x1 r1) (my_Fix_F x2 r2).
Proof.
  intro x1; induction (Rwf x1); intros x2 r1 r2.
  rewrite <- (my_Fix_F_eq x r1); rewrite <- (my_Fix_F_eq x2 r2); intros.
  apply F_ext; auto.
Qed.

Lemma my_Fix_eq : forall (x1 x2:A),
    E1 x1 x2 -> E2 (my_Fix x1) (F x2 (fun (y:A) (p:R y x2) => my_Fix y)).
Proof.
  intro x; unfold my_Fix.
  rewrite <- my_Fix_F_eq.
  intros. apply F_ext; intros.
  - assumption.
  - apply my_Fix_F_inv. assumption.
Qed.

End FixPoint.

Require Import bedrock2.Semantics.
Require Import compiler.FlatImp.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Wf Relation_Operators Wellfounded.
Require Import riscv.Utility.Utility.

Section WithWord.
  Context {width} {BW: Bitwidth width} {word: word.word width}.
  
  Definition lt_tuple' : abstract_trace * stmt Z -> abstract_trace * stmt Z -> Prop := slexprod _ _ abstract_trace_lt stmt_lt.
  
  Lemma lt_tuple'_wf : well_founded lt_tuple'.
  Proof.
    apply wf_slexprod.
    - apply wf_abstract_trace_lt.
    - apply wf_stmt_lt.
  Defined.
  
  Definition Let_In_pf_nd {A B} (x : A) (f : forall a : A, a = x -> B) : B := let y := x in f y eq_refl.
  
  Lemma Let_In_pf_nd_ext {A B} (E : B -> B -> Prop) (x : A) (f1 f2 : forall a : A, a = x -> B) :
    (forall x1 x2, E (f1 x1 x2) (f2 x1 x2)) ->
    E (Let_In_pf_nd x f1) (Let_In_pf_nd x f2).
  Proof. intros. cbv [Let_In_pf_nd]. apply H. Qed.
End WithWord.
