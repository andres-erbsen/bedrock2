Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap := func! (a, b) {
  t = load(b);
  store(b, load(a));
  store(a, t)
}.

Definition bad_swap := func! (a, b) {
  store(b, load(a));
  store(a, load(b))
}.

Definition swap_swap := func! (a, b) {
  swap(a, b);
  swap(a, b)
}.

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.rdelta.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Instance spec_of_swap : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ (filterio T) = (filterio t) }.
  
  Instance ct_swap : ct_spec_of "swap" :=
    ctfunc! "swap" a_addr b_addr | (dummy1 : nat) / (dummy2 : nat) | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R }.
  
  Instance ct_bad_swap : ct_spec_of "bad_swap" :=
    ctfunc! "bad_swap" a_addr | b_addr / (dummy : nat) | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R }.
  
  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof. repeat straightline; eauto. Qed.

  Lemma swap_ct : program_logic_ct_goal_for_function! swap.
  Proof. repeat straightline. subst t''0. subst t''. subst t'0.
         Search (_ :: _ = _ ++ _).
         instantiate (1 := [write access_size.word a_addr;
                            write access_size.word b_addr;
                            Semantics.read access_size.word a_addr;
                            Semantics.read access_size.word b_addr]).
  reflexivity. Qed.

  Instance spec_of_bad_swap : spec_of "bad_swap" :=
    fnspec! "bad_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ (filterio T) = (filterio t) }.
  Lemma bad_swap_ok : program_logic_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.

  Lemma bad_swap_ct : program_logic_ct_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.

  Definition spec_of_swap_same : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a R,
    { requires t m := m =* scalar a_addr a * R /\ b_addr = a_addr;
      ensures T M :=  M =* scalar a_addr a * R /\ (filterio T) = (filterio t) }.

  Lemma swap_same_ok :
    let spec_of_swap := spec_of_swap_same in
    program_logic_goal_for_function! swap.
  Proof. repeat straightline; eauto. Qed.

  Instance spec_of_swap_swap : spec_of "swap_swap" :=
    fnspec! "swap_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr a * scalar b_addr b * R /\ (filterio T) = (filterio t)}.

  Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
  Proof. repeat (straightline || straightline_call); eauto using eq_trans. Qed.

  Lemma link_swap_swap_swap_swap : spec_of_swap_swap &[,swap_swap; swap].
  Proof. eauto using swap_swap_ok, swap_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module &[,swap_swap; swap]). Abort.
  *)
End WithParameters.
