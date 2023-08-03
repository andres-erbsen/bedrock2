Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.

Import Syntax.Coercions BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition stacktrivial := func! { stackalloc 4 as t; /*skip*/ }.

Definition stacknondet := func! () ~> (a, b) {
  stackalloc 4 as t;
  a = (load4(t) >> $8);
  store1(t, $42);
  b = (load4(t) >> $8)
}.

Definition stackdisj := func! () ~> (a,b) {
  stackalloc 4 as a;
  stackalloc 4 as b;
  /*skip*/
}.

Definition stackswap := func! (a, b) ~> (b, a) {
  stackalloc 4 as x;                          
  store(x, a);
  stackalloc 4 as y;                          
  store(y, b);
  swap(y, x);
  a = load(x);
  b = load(y)
}.

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import bedrock2Examples.swap.
Require Import coqutil.Word.Interface.
From coqutil.Tactics Require Import reference_to_string .
From bedrock2 Require ToCString PrintListByte.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Instance spec_of_stacktrivial : spec_of "stacktrivial" := fun functions => forall stack_addr m t,
      WeakestPrecondition.call stack_addr functions
        "stacktrivial" t m [] (fun t' m' rets => rets = [] /\ m'=m /\ (filterleakage t')=(filterleakage t)).

  Lemma stacktrivial_ok : program_logic_goal_for_function! stacktrivial.
  Proof.
    repeat straightline.

    set (R := eq m).
    pose proof (eq_refl : R m) as Hm.

    repeat straightline.

    (* test for presence of intermediate separation logic hypothesis generated by [straightline_stackalloc] *)
    lazymatch goal with H : Z.of_nat (Datatypes.length ?stackarray) = 4 |- _ =>
    lazymatch goal with H : sep _ _ _ |- _ =>
    lazymatch type of H with context [Array.array ptsto _ ?a stackarray] =>
    idtac
    end end end.

    intuition congruence.
  Qed.

  Definition stackall := func! () ~> () {
  stackalloc 4 as a;
  x = load4(a)
                           }.

  (*should fix notation so this works
Instance ct_spec_of_stackall : ct_spec_of "stackall" :=
    ctfunc! "stackall" | / |,
      { requires tr mem := True }.*)

  (*Lemma stackall_ct : program_logic_goal_for_function! stackall.
  Proof.
    repeat straightline.
    set (R := eq mem0).
    pose proof (eq_refl : R mem0) as Hmem0.
    straightline_stackalloc. eexists. eexists. split.
    { repeat straightline. eexists. split; repeat straightline. Print ptsto.
      repeat (destruct stack as [|?b stack]; try solve [cbn in H3; Lia.lia]; []).
      repeat straightline.
      clear H2.
      Print seprewrite0_in.
      seprewrite_in_by @scalar32_of_bytes Hmem0 reflexivity.
      repeat straightline. }
    repeat straightline. simpl. instantiate (1 := [_]). simpl. f_equal. eauto.
    rewrite H. eauto.
  Qed.*)

  Instance ct_spec_of_stackswap : spec_of "stackswap" :=
    ctfunc! "stackswap" | a b / | ~> B A,
      { requires tr mem := True ; ensures tr' mem' := B = a /\ A = b }.
  Search (spec_of "swap").
  Lemma stackswap_ct :
    let swapspec := ct_spec_of_swap in
    program_logic_goal_for_function! stackswap.
  Proof.
    straightline. Print straightline.
    (* TODO: integrate below into straightline. *)
    match goal with
    | |- program_logic_goal_for ?f _ =>
        idtac "2A"; enter f; intros end. cbv [swapspec ct_spec_of_swap] in H.
    repeat match goal with
    | stack_addr : stack_trace -> Z -> ?word, H: (forall (_ : stack_trace -> Z -> ?word), _) |- _ => let f := fresh "f" in
        idtac H; assert (H := H stack_addr); destruct H as [f H] end.
         match goal with
         | |- call _ _ _ _ _ _ _ => idtac
         | _ => eexists
         end. intros; unfold1_call_goal; cbv beta match delta [call_body];
         lazymatch goal with
         | |- if ?test then ?T else _ => replace test with true by reflexivity; change T
         end; cbv beta match delta [func].
    repeat straightline.
    set (R := eq mem0).
    pose proof (eq_refl : R mem0) as Hmem0.
    repeat straightline.
    repeat (destruct stack as [|?b stack]; try solve [cbn in H3; Lia.lia]; []).
    clear H3. clear length_stack. clear H1. (*clear Hmem1.
    subst R. *)
    seprewrite_in_by @scalar_of_bytes Hmem0 reflexivity.
    repeat straightline.
    repeat (destruct stack as [|?b stack]; try solve [cbn in length_stack; Lia.lia]; []).
    clear H6 length_stack H3.
    seprewrite_in_by @scalar_of_bytes H1 reflexivity.
    repeat straightline. 
    (*destruct H8 as [m1_1 [m1_2 [H8_1 [H8_2 [m1_2_1 [m1_2_2 H8_3]]]]]].*)
    Print straightline_ct_call. Search (exists _, _ -> _).
    assert (HToBytesa: exists n0 n1 n2 n3, a = word.of_Z (LittleEndianList.le_combine [n0; n1; n2; n3])). { admit. }
    assert (HToBytesb: exists n4 n5 n6 n7, b = word.of_Z (LittleEndianList.le_combine [n4; n5; n6; n7])). { admit. }
      destruct HToBytesa as [n0 [n1 [n2 [n3 HToBytesa]]]].
    destruct HToBytesb as [n4 [n5 [n6 [n7 HToBytesb]]]].
    subst a b.
        (*TODO: put this in ProgramLogic, name it straightline_ct_call or something*)

    lazymatch goal with
  | |- call _ ?functions ?callee _ _ _ _ =>
        (*let callee_spec := lazymatch constr:((_ : spec_of callee)) with
                           | ?s => s
                           end in*)
        let Hcall := lazymatch goal with
                     | H: context [ call _ functions callee _ _ _ _ ] |- _ => H
                     end in
         eapply WeakestPreconditionProperties.Proper_call; cycle
         -1; [ eapply Hcall | try eabstract solve [ Morphisms.solve_proper ].. ];
         [ .. | intros ? ? ? ? ]
    end; eauto.
    - apply sep_assoc. eassumption.
    - apply locals_ok.
    - apply env_ok.
    - apply ext_spec_ok.
    - repeat straightline.
      Import symmetry eplace. Check @scalar_of_bytes. 
      seprewrite_in_by (symmetry! @scalar_of_bytes) H8 reflexivity.
      assert (length [n0; n1; n2; n3] = 4%nat) by reflexivity.
      straightline_stackdealloc.
      seprewrite_in_by (symmetry! @scalar_of_bytes) H8 reflexivity.
      assert (length [n4; n5; n6; n7] = 4%nat) by reflexivity.
      straightline_stackdealloc.
      repeat straightline. split.
      2: { repeat straightline. }
      trace_alignment.
      (* only the word-to-bytes admits remain *)
  Abort.
  
  Instance spec_of_stacknondet : spec_of "stacknondet" := fun functions => forall stack_addr m t,
      WeakestPrecondition.call stack_addr functions
        "stacknondet" t m [] (fun t' m' rets => exists a b, rets = [a;b] /\ a = b /\ m'=m/\(filterio t')=(filterio t)).

  Add Ring wring : (Properties.word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Lemma stacknondet_ok : program_logic_goal_for_function! stacknondet.
  Proof.
    repeat straightline.
    set (R := eq m).
    pose proof (eq_refl : R m) as Hm.
    repeat straightline.
    repeat (destruct stack as [|?b stack]; try solve [cbn in H1; Lia.lia]; []);
      clear H H0 H1 length_stack.
    seprewrite_in_by @scalar32_of_bytes Hm reflexivity.
    repeat straightline.
    Import symmetry eplace.
    seprewrite_in_by (symmetry! @scalar32_of_bytes) Hm reflexivity.
    cbn [Array.array] in Hm.
    Import Ring_tac.
    repeat straightline.
    assert ((Array.array ptsto (word.of_Z 1) a [(Byte.byte.of_Z (word.unsigned v0)); b0; b1; b2] ⋆ R)%sep m1).
    { cbn [Array.array].
      use_sep_assumption; cancel; Morphisms.f_equiv; f_equal; f_equal; ring. }
    seprewrite_in_by @scalar32_of_bytes H0 reflexivity.
    repeat straightline.
    seprewrite_in_by (symmetry! @scalar32_of_bytes) H0 reflexivity.
    Print straightline_stackdealloc.
    repeat straightline.
    set [Byte.byte.of_Z (word.unsigned v0); b0; b1; b2] as ss in *.
    assert (length ss = Z.to_nat 4) by reflexivity.
    Print straightline_stackdealloc. subst a.
    repeat straightline.
    Tactics.ssplit; eauto.

    subst v. subst v1. subst ss.
    eapply Properties.word.unsigned_inj.
    rewrite ?Properties.word.unsigned_sru_nowrap.
    2,3: rewrite ?Properties.word.unsigned_of_Z_nowrap by Lia.lia; reflexivity.
    rewrite ?Properties.word.unsigned_of_Z_nowrap; try Lia.lia.
    2,3: eapply (LittleEndianList.le_combine_bound [_;_;_;_]).
    repeat change [?a;?b;?c;?d] with ([a]++[b;c;d]).
    rewrite 2LittleEndianList.le_combine_app, 2LittleEndianList.le_combine_1, 2Z.shiftr_lor; simpl Z.of_nat; f_equal.
    rewrite 2Z.shiftr_div_pow2, 2Zdiv.Zdiv_small; eauto using Byte.byte.unsigned_range; Lia.lia.
  Qed.

  Import ToCString PrintListByte.
  Definition stacknondet_main := func! () ~> ret {
      unpack! a, b = stacknondet();
      ret = a ^ b
  }.
  Definition stacknondet_c := String.list_byte_of_string (c_module (("main",stacknondet_main)::("stacknondet",stacknondet)::nil)).
  (* Goal True. print_list_byte stacknondet_c. Abort. *)

  Instance spec_of_stackdisj : spec_of "stackdisj" := fun functions => forall m t,
      WeakestPrecondition.call functions
        "stackdisj" t m [] (fun t' m' rets => exists a b, rets = [a;b] /\ a <> b /\ m'=m/\t'=t).

  Lemma stackdisj_ok : program_logic_goal_for_function! stackdisj.
  Proof.
    repeat straightline.
    set (R := eq m).
    pose proof (eq_refl : R m) as Hm.
    repeat straightline.
    repeat esplit.
    all : try intuition congruence.
    match goal with |- _ <> _ => idtac end.
  Abort.
End WithParameters.
