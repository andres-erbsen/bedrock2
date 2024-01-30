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

Definition stackalloc_and_print :=
  func! () {
      stackalloc 4 as x;
      output! MMIOWRITE($0, x)
    }.

Definition io_function :=
  func! () {
      io! y = MMIOREAD($0);
      io! x = MMIOREAD($0);
      if (x) { /*skip*/ }
    }.

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require Import bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.rdelta.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  (*Instance ct_spec_of_swap : spec_of "swap" :=
    ctfunc! "swap" a_addr b_addr | / | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ T = t }.*)

  Instance ct_spec_of_swap : spec_of "swap" :=
    fun functions =>
      exists f : word -> word -> trace,
      forall (k : trace) (t : io_trace) (m : mem) (a_addr b_addr a b : word) (R : mem -> Prop),
        (scalar a_addr a ⋆ scalar b_addr b ⋆ R)%sep m ->
        call functions "swap" k t m [a_addr; b_addr]
          (fun (k' : trace) (T : io_trace) (M : mem) (rets : list word) =>
             M =* scalar a_addr b * scalar b_addr a * R /\ T = t /\ rets = [] /\
             exists k'',
               k' = k'' ++ k /\ k'' = f a_addr b_addr
          ).

  Instance ct_spec_of_io_function : spec_of "io_function" :=
    fun functions =>
      exists f,
      forall k t m (R : _ -> Prop),
        m =* R ->
        isMMIOAddr (word.of_Z 0) ->
        WeakestPrecondition.call
          functions "io_function" k t m nil
          (fun k' t' m' rets =>
             exists x y,
               t' = [((map.empty, "MMIOREAD", [word.of_Z 0]), (map.empty, [x]));
                     ((map.empty, "MMIOREAD", [word.of_Z 0]), (map.empty, [y]))] ++ t /\
                 m =* R /\
                 exists k'',
                   k' = k'' ++ k /\
                     k'' = f x).

  Instance ct_spec_of_stackalloc_and_print : spec_of "stackalloc_and_print" :=
    fun functions =>
      forall pick_sp,
      exists output_event,
      forall (k : trace) (t : io_trace) (m : mem),
        isMMIOAddr (word.of_Z 0) ->
        call functions "stackalloc_and_print" k t m []
          (fun (k' : trace) (T : io_trace) (M : mem) (rets : list word) =>
             exists k'',
               k' = k'' ++ k /\
                 (predicts pick_sp (List.rev k'') ->
                  T = output_event :: t)). 

  (* I should make this work again.
Instance ct_bad_swap : ct_spec_of "bad_swap" :=
    ctfunc! "bad_swap" | a_addr b_addr / | a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R }.*)
  
  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof. repeat straightline. intuition eauto. eexists. split.
         { trace_alignment. }
         reflexivity.
  Qed.

  Lemma io_function_ok : program_logic_goal_for_function! io_function.
  Proof.
    repeat straightline.
    econstructor.
    repeat straightline.
    exists m, map.empty.
    split.
    { apply Properties.map.split_empty_r. reflexivity. }
    cbv [ext_spec]. replace (String.eqb _ _) with false by reflexivity.
    replace (String.eqb _ _) with true by reflexivity.
    repeat straightline.
    split; [repeat straightline|].
    { split; [assumption|]. Search (word.unsigned (word.of_Z 0)).
      rewrite Properties.word.unsigned_of_Z_0. reflexivity. }
    intros.
    econstructor.
    repeat straightline.
    split. { subst l. reflexivity. }
    repeat straightline.
    econstructor.
    repeat straightline.
    exists m, map.empty.
    split.
    { assumption. }
    cbv [ext_spec]. replace (String.eqb _ _) with false by reflexivity.
    replace (String.eqb _ _) with true by reflexivity.
    eexists.
    split; [reflexivity|].
    split.
    { split; [reflexivity|]. split; [assumption|]. Search (word.unsigned (word.of_Z 0)).
      rewrite Properties.word.unsigned_of_Z_0. reflexivity. }
    repeat straightline.
    econstructor.
    repeat straightline.
    split; repeat straightline.
    { eexists. eexists. split.
      { reflexivity. }
      repeat straightline. split; [assumption|].
      eexists. split.
      { subst k'. instantiate (1 := [_; _; _]). reflexivity. }
      Check word.eqb. Check (fun x => _ _ aleak_bool ((word.unsigned x) =? 0)).
      instantiate (1 := fun val0 => match (word.unsigned val0 =? 0)%Z with
                                    | true => _
                                    | false => _
                                    end).
      simpl. apply Z.eqb_neq in H3. rewrite H3. intros. reflexivity. }
    eexists. eexists. split.
    { reflexivity. }
    repeat straightline. split; [assumption|].
    eexists. split.
    { subst k'0 k'. instantiate (1 := [_; _; _]). reflexivity. }
    Check word.eqb. Check (fun x => aleak_bool ((word.unsigned x) =? 0) _).
    simpl.
    rewrite <- Z.eqb_eq in H3. rewrite H3. intros. reflexivity. 
  Qed.

  Lemma stackalloc_and_print_ok : program_logic_goal_for_function! stackalloc_and_print.
  Proof.
    repeat straightline.
    eapply interact_nomem.
    { repeat straightline. }
    cbv [ext_spec]. simpl.
    repeat straightline. intuition.
    { rewrite Properties.word.unsigned_of_Z_0. reflexivity. }
    repeat straightline. eexists. eexists. split; [eassumption|]. split; [eassumption|].
    eexists. split.
    { instantiate (1 := [_; _]). reflexivity. }
    intros Hpredicts. simpl in Hpredicts.
    inversion Hpredicts. subst. specialize (H5 I).
    instantiate (1 := match pick_sp [] with
                      | consume_word a => _
                      | _ => _
                      end).
    rewrite H5. reflexivity.
    Unshelve. Print io_event.
    all: exact (map.empty, "", [], (map.empty, [])).
  Qed.


  (*Lemma swap_ct : program_logic_ct_goal_for_function! swap.
  Proof. repeat straightline. trace_alignment. Qed.*)

  (*I don't think there's any io spec that will make this one constant-time.
    What we'd want to do is say that the output must be the secret if we're supposed to leak it,
    but there's no way to say that in the io spec, since we dont' know what the secret is.
    So, if we want to say that this is constant-time, then we have to do some silly things with
    the function specification.*)
  (* can reference (call set_channel1) and inputs to set_channel1 in IO spec to constrain this.*)
                      
    
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
    fixed input, so it's not clear what to do here so that the trace is constant.
    We can do ugly (non-general) things: could make function spec say
    (final trace indicates that the input is public) ->
    (final trace generated by our fixed abstract trace).
*)
  Definition set_channel2 :=
    func! () {
        io! input_is_public = IS_PUBLIC();
        io! input = IN();
        if (input_is_public)
             {
               if (input) { /*skip*/ }
             }
      }.

  Definition set_channel4 :=
    func! (input_is_public) {
        io! nothing = OUT(input_is_public);
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

  (*sure, we can do this - but somewhat stupidly.  But what if we wanted to allow leaking other functions of the secret?  Only works if the function is known ahead of time.*)
  (*we won't include io events in leakage trace, so nothing interesting here*)
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

  (*should have postcondition of the form
    (exists input, tr' = f input /\ io_spec tr' input), where tr' is trace after function is done.*)

  (*we can do this using IO trace, sorta.*)
  Definition leak_once1 :=
    func!() {
        io! input = IN();
        io! out = OUT(input)
      }.

  Definition leak_once1_bad :=
    func!() {
        io! input = IN();
        io! out = OUT(input);
        io! out = OUT(input)
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
        
  
  Print io_event.

  (*Instance ext_spec: ExtSpec :=
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
        end.*)

  Instance spec_of_bad_swap : spec_of "bad_swap" :=
    fnspec! "bad_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr b * scalar b_addr a * R /\ T = t }.
  Lemma bad_swap_ok : program_logic_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.

  (*Lemma bad_swap_ct : program_logic_ct_goal_for_function! bad_swap.
  Proof. repeat straightline; eauto. Abort.*)

  Definition spec_of_swap_same : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a R,
    { requires t m := m =* scalar a_addr a * R /\ b_addr = a_addr;
      ensures T M :=  M =* scalar a_addr a * R /\ T = t }.

  Lemma swap_same_ok :
    let spec_of_swap := spec_of_swap_same in
    program_logic_goal_for_function! swap.
  Proof. repeat straightline; eauto. Qed.

  Instance spec_of_swap_swap : spec_of "swap_swap" :=
    fnspec! "swap_swap" a_addr b_addr / a b R,
    { requires t m := m =* scalar a_addr a * scalar b_addr b * R;
      ensures T M :=  M =* scalar a_addr a * scalar b_addr b * R /\ T = t }.

  (*Lemma swap_swap_ok :
    let spec_of_swap := ct_spec_of_swap in program_logic_goal_for_function! swap_swap.
  Proof.
    repeat (straightline || straightline_ct_call); eauto using eq_trans.
    straightline_call.
  Qed.*)

  (*Lemma link_swap_swap_swap_swap : spec_of_swap_swap &[,swap_swap; swap].
  Proof. eauto using swap_swap_ok, swap_ok. Qed.*)

  (* Print Assumptions link_swap_swap_swap_swap. *)
  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module &[,swap_swap; swap]). Abort.
   *)

  

  Definition weird_function :=
    func! () {
        io! y = MMIOREAD($0);
        io! x = MMIOREAD($0);
        stackalloc 4 as a;
        stackalloc 4 as b;
        if (a < b) {
               if (x){
                      /*skip*/
                    }
             }
      }.

  (*Instance ext_spec : ExtSpec :=
    fun t mGive action (argvals: list word) (post: (mem -> list word -> Prop)) =>
      match argvals with
      | nil => if String.eqb action "INPUT" then
                 mGive = map.empty /\
                 forall input, post map.empty [input]
               else False
      | _ => False
      end.*)

  Print io_event.

  
  
  
End WithParameters.
