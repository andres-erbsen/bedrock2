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

  Instance ct_spec_of_swap : spec_of "swap" :=
    ctfunc! "swap" a_addr b_addr | / | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ (filterio T) = (filterio t) }.

  (* I should make this work again.
Instance ct_bad_swap : ct_spec_of "bad_swap" :=
    ctfunc! "bad_swap" | a_addr b_addr / | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R }.*)
  
  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof. repeat straightline. split; repeat straightline. 2: split; trace_alignment; repeat straightline; auto.
         eexists. split. 2: trace_alignment. repeat constructor. Qed.

  (*Lemma swap_ct : program_logic_ct_goal_for_function! swap.
  Proof. repeat straightline. trace_alignment. Qed.*)

  (*I don't think there's any io spec that will make this one constant-time.
    What we'd want to do is say that the output must be the secret if we're supposed to leak it,
    but there's no way to say that in the io spec, since we dont' know what the secret is.
    So, if we want to say that this is constant-time, then we have to do some silly things with
    ghost constants in the function specification.*)
  Definition set_channel1 :=
    func! (input) {
        io! input_is_public = IS_PUBLIC();
        x = $5;
        if (input_is_public) { x = input };
          io! nothing = OUT(x)
      }.

  Definition set_channel1_bad :=
    func! (input) {
        io! input_is_public = IS_PUBLIC();
        io! nothing = OUT(input)
      }.

  (*This one has a different issue, but it's still an issue.  We can't say that there is some 
    fixed input, so it's not clear what to do here so that the trace is constant.*)
  Definition set_channel2 :=
    func! () {
        io! input_is_public = IS_PUBLIC();
        io! input = IN();
        if (input_is_public)
             {
               if (input) { /*skip*/ }
             }
      }.
  
  Definition set_channel2_bad :=
    func! () {
        io! input_is_public = IS_PUBLIC();
        io! input = IN();
        if (input) { /*skip*/ }
      }.

  Definition set_channel3 :=
    func! () {
        io! input_is_public = IS_PUBLIC();
        io! input = IN();
        x = $5;
        if (input_is_public) { x = input };
          io! nothing = OUT(x)
      }.
  
  Definition set_channel3_bad :=
    func! () {
        io! input_is_public = IS_PUBLIC();
        io! input = IN();
        io! nothing = OUT(input)
      }.

(*
idea: give ExtSpec an additional parameter, leak : list word -> list word, which given the 
inputs to the bedrock2 program, gives things that can be leaked.
    
limitation of this: we can't say that sometimes it's ok to leak secrets by outputting them.

solution: give it another parameter, which given the outputs of the bedrock2 program,
gives things that are ok to be secrets.

Remaining problem: these fancy parameters propagate down to the assembly level and get involved 
in the assembly-level trace.
*)

  (*Can we write two io specs, one of which says this is constant-time and the other doesn't?
    I think not.
    Of course, we can write two function specs, one saying that this is ok and one not.*)
  Definition output_secret :=
    func! (secret) {
        io! x = OUT(secret)
      }.

  (*Can we write two io specs, one of which says this is constant-time and the other doesn't?
    Yes, easily.*)
  Definition output_secret2 :=
    func! () {
        io! secret = IN();
        io! x = OUT(secret)
      }.

  Definition leakfxthenx :=
    func! (secret) {
        
  
  Print io_event.

  Instance ext_spec: ExtSpec :=
      fun t mGive action (argvals: list word) (post: (mem -> list word -> Prop)) =>
        match argvals with
        | nil => if String.eqb action "IN" then
                   forall secret, post map.empty [secret]
                 else False
        | [addr] =>
            if String.eqb action "OUT" then
              match t with
              | IO (_, _, _, (_, leak_secret)) =>
                  post map.empty [
            argvals = [addr] /\ forall val, post map.empty [val]
          else if String.eqb action MMOutput then
                 exists val, argvals = [addr; val] /\ post map.empty nil
          else False
        | nil => False
        end.

  Instance spec_of_bad_swap : spec_of "bad_swap" :=
    fnspec! "bad_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ (filterio T) = (filterio t) }.
  Lemma bad_swap_ok : program_logic_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.

  (*Lemma bad_swap_ct : program_logic_ct_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.*)

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

  Lemma swap_swap_ok :
    let spec_of_swap := ct_spec_of_swap in program_logic_goal_for_function! swap_swap.
  Proof. repeat (straightline || straightline_ct_call); eauto using eq_trans. Qed.

  Lemma link_swap_swap_swap_swap : spec_of_swap_swap &[,swap_swap; swap].
  Proof. eauto using swap_swap_ok, swap_ok. Qed.

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module &[,swap_swap; swap]). Abort.
  *)
End WithParameters.
