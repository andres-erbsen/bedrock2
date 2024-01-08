Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.MemoryLayout.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require bedrock2.Hexdump.
Require Import bedrock2Examples.swap.
Require Import bedrock2Examples.stackalloc.
Require Import compilerExamples.SpillingTests.
Require compiler.NaiveRiscvWordProperties.

Require Import compiler.util.Common.


Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Definition var: Set := Z.
Definition Reg: Set := Z.


Local Existing Instance DefaultRiscvState.

Axiom TODO: forall {T: Type}, T.

Local Instance funpos_env: map.map string Z := SortedListString.map _.

Definition compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: FlatImp.stmt Z) :=
  match s with
  | FlatImp.SInteract _ fname _ =>
    if string_dec fname "nop" then
      [[Addi Register0 Register0 0]]
    else
      nil
  | _ => []
  end.

Notation RiscvMachine := MetricRiscvMachine.

Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.

Definition main_stackalloc := func! {
  stackalloc 4 as x; stackalloc 4 as y; swap_swap(x, y) }.

Definition allFuns := &[,swap; swap_swap; main_stackalloc; stacknondet; stackdisj; long1].

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-8), next stack word to (stack_pastend-16) etc *)
Definition stack_pastend: Z := 2048.

Lemma f_equal2: forall {A B: Type} {f1 f2: A -> B} {a1 a2: A},
    f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof. intros. congruence. Qed.

Lemma f_equal3: forall {A B C: Type} {f1 f2: A -> B -> C} {a1 a2: A} {b1 b2: B},
    f1 = f2 -> a1 = a2 -> b1 = b2 -> f1 a1 b1 = f2 a2 b2.
Proof. intros. congruence. Qed.

Lemma f_equal3_dep: forall {A B C: Type} {f1 f2: A -> B -> C} {a1 a2: A} {b1 b2: B},
    f1 = f2 -> a1 = a2 -> b1 = b2 -> f1 a1 b1 = f2 a2 b2.
Proof. intros. congruence. Qed.


Local Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
Proof. reflexivity. Qed.

Definition swap_asm: list Instruction.
  let r := eval cbv in (compile compile_ext_call allFuns) in set (res := r).
  match goal with
  | res := Success (?x, _, _) |- _ => exact x
  end.
Defined.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold swap_asm in swap_asm in idtac (* r *). Abort.
  (*
  swap_swap:
     addi    x2, x2, -20   // decrease sp
     sw      x2, x1, 8     // save ra
     sw      x2, x3, 0     // save registers modified by swap_swap
     sw      x2, x4, 4
     lw      x3, x2, 12    // load args
     lw      x4, x2, 16
     sw      x2, x3, -8    // store args for first call to swap
     sw      x2, x4, -4
     jal     x1, 36        // first call to swap
     sw      x2, x3, -8    // store args for second call to swap
     sw      x2, x4, -4
     jal     x1, 24        // second call to swap
     lw      x3, x2, 0     // restore registers modified by swap_swap
     lw      x4, x2, 4
     lw      x1, x2, 8     // load ra
     addi    x2, x2, 20    // increase sp
     jalr    x0, x1, 0     // return

  swap:
     addi    x2, x2, -28   // decrease sp
     sw      x2, x1, 16    // save ra
     sw      x2, x5, 0     // save registers modified by swap
     sw      x2, x6, 4
     sw      x2, x3, 8
     sw      x2, x4, 12
     lw      x3, x2, 20    // load args
     lw      x4, x2, 24
     lw      x5, x4, 0     // body of swap
     lw      x6, x3, 0
     sw      x4, x6, 0
     sw      x3, x5, 0
     lw      x5, x2, 0     // restore registers modified by swap
     lw      x6, x2, 4
     lw      x3, x2, 8
     lw      x4, x2, 12
     lw      x1, x2, 16    // restore ra
     addi    x2, x2, 28    // increase sp
     jalr    x0, x1, 0     // return

  stacknondet:
     addi    x2, x2, -56
     sw      x2, x1, 44
     sw      x2, x5, 4
     sw      x2, x6, 8
     sw      x2, x7, 12
     sw      x2, x3, 16
     sw      x2, x8, 20
     sw      x2, x9, 24
     sw      x2, x10, 28
     sw      x2, x11, 32
     sw      x2, x12, 36
     sw      x2, x4, 40
     addi    x5, x2, 0
     lw      x6, x5, 0
     addi    x7, x0, 8
     srl     x3, x6, x7
     addi    x8, x0, 3
     add     x9, x3, x8
     addi    x10, x0, 42
     sb      x9, x10, 0
     lw      x11, x5, 0
     addi    x12, x0, 8
     srl     x4, x11, x12
     sw      x2, x3, 48
     sw      x2, x4, 52
     lw      x5, x2, 4
     lw      x6, x2, 8
     lw      x7, x2, 12
     lw      x3, x2, 16
     lw      x8, x2, 20
     lw      x9, x2, 24
     lw      x10, x2, 28
     lw      x11, x2, 32
     lw      x12, x2, 36
     lw      x4, x2, 40
     lw      x1, x2, 44
     addi    x2, x2, 56
     jalr    x0, x1, 0

  stackdisj:
     addi    x2, x2, -28
     sw      x2, x1, 16
     sw      x2, x3, 8
     sw      x2, x4, 12
     addi    x3, x2, 4
     addi    x4, x2, 0
     sw      x2, x3, 20
     sw      x2, x4, 24
     lw      x3, x2, 8
     lw      x4, x2, 12
     lw      x1, x2, 16
     addi    x2, x2, 28
     jalr    x0, x1, 0

  main:
     addi    x2, x2, -20   // decrease sp
     sw      x2, x1, 16    // save ra
     sw      x2, x3, 8     // save registers modified by main
     sw      x2, x4, 12
     addi    x3, x2, 4     // first stackalloc invocation returns sp+4
     addi    x4, x2, 0     // second stackalloc invocation returns sp
     sw      x2, x3, -8    // store args for call to swap_swap
     sw      x2, x4, -4
     jal     x1, -380      // call swap_swap
     lw      x3, x2, 8     // restore registers modified by main
     lw      x4, x2, 12
     lw      x1, x2, 16    // restore ra
     addi    x2, x2, 20    // increase sp
     jalr    x0, x1, 0     // return
  *)
End PrintAssembly.

Definition swap_as_bytes: list Byte.byte := instrencode swap_asm.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval cbv in swap_as_bytes in idtac (* x *). Abort.
End PrintBytes.


Check (&[,swap_swap; swap]).
Check compiler_correct_wp.
Print compiler_correct_wp.
Print ExtSpec.
Context {mem : map.map Words32Naive.word byte}.
Context {mem_ok : map.ok mem}.
Context {localsL : map.map Z Words32Naive.word}.
Context {localsL_ok : map.ok localsL}.
Context {localsH : map.map string Words32Naive.word}.
Context {localsH_ok : map.ok localsH}.
Context {envL : map.map string (list Z * list Z * FlatImp.stmt Z)}.
Context {envH : map.map string (list string * list string * cmd)}.
Context {envH_ok : map.ok envH}.
(*Context {M : Type -> Type} {MM : Monad M}.*)
(*Context {RVM: RiscvProgramWithLeakage}.
Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
Context {PR: MetricPrimitives PRParams}.*)
Search ExtSpec.

Require Import compiler.MMIO.
Import bedrock2.FE310CSemantics.
(*Lemma ext_spec_ok : ext_spec.ok ext_spec.
Proof.
  constructor; intros; cbv [bedrock2Examples.swap.ext_spec ext_spec] in *.
  - destruct args; [|destruct H]. destruct (_ =? _); [|destruct H].
    destruct H as [H _]. destruct H0 as [H0 _]. subst. apply map.same_domain_refl.
  - cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl].
    intros. destruct args; [|destruct H0]. destruct (_ =? _); [|destruct H0].
    destruct H0 as [H1 H2]. split; auto.
  - destruct args; [|destruct H]. destruct (_ =? _); [|destruct H]. destruct H as [H1 H2].
    destruct H0 as [H3 H4]. auto.
Qed.

Print bedrock2Examples.swap.ext_spec. Print Byte.xa0.

Definition other_compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: FlatImp.stmt Z) :=
  match s with
  | FlatImp.SInteract _ fname _ =>
    if string_dec fname "INPUT" then
      [[Addi 1 Register0 7]]
    else
      nil
  | _ => []
  end.
Definition other_leak_ext_call : funpos_env -> Z -> Z -> FlatImp.stmt Z -> list LeakageEvent :=
  fun _ _ _ _ => nil.*)
Search LeakExt.
Check leak_ext_call.
Print compile_ext_call.

Check (@FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I _ _ _ _ _ compile_ext_call
         leak_ext_call _ _ _ _ _ _ _ _ _ compile_ext_call).
Check @compiler_correct_wp.
(*Check (@PrimitivesParams _ _ _ _ _ M MetricRiscvMachine).
Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _).*)
Check NaiveRiscvWordProperties.naive_word_riscv_ok.
Lemma word_ok : RiscvWordProperties.word.riscv_ok Words32Naive.word.
Proof.
  cbv [Words32Naive.word]. replace 32 with (2 ^ BinInt.Z.of_nat 5) by reflexivity.
  apply NaiveRiscvWordProperties.naive_word_riscv_ok.
Qed.

Lemma word_ok' : word.ok Words32Naive.word.
Proof.
  Search (word.ok _). cbv [Words32Naive.word]. exact Naive.word32_ok. Qed.

Check compile_ext_call_correct.

(*Lemma compile_ext_call_works :
  (forall (resvars : list Z) (extcall : string) (argvars : list Z),
        @FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I 32 Bitwidth32.BW32
          Words32Naive.word localsL (SortedListString.map Z) (@compile_ext_call SortedListString.map) (@leak_ext_call Words32Naive.word SortedListString.map) mem
          (SortedListString.map (list Z * list Z * FlatImp.stmt Z)) M MM RVM PRParams ext_spec
          leak_ext RV32I_bitwidth compile_ext_call (@FlatImp.SInteract Z resvars extcall argvars)).
Proof.
  intros. Search compile_ext_call. cbv [FlatToRiscvCommon.compiles_FlatToRiscv_correctly]. intros.
  apply compile_ext_call_correct. exfalso. clear -H.
  inversion H. subst. cbv [ext_spec] in *. assumption.
Qed.*)

Lemma compile_ext_call_length :
  (forall (stackoffset : Z) (posmap1 posmap2 : SortedListString.map Z) 
          (c : FlatImp.stmt Z) (pos1 pos2 : Z),
        @Datatypes.length Instruction (compile_ext_call posmap1 pos1 stackoffset c) =
          @Datatypes.length Instruction (compile_ext_call posmap2 pos2 stackoffset c)).
Proof.
  intros. cbv [compile_ext_call]. reflexivity. Qed.
Definition fs_swap := &[,swap].
Definition instrs_swap :=
  match (compile compile_ext_call fs_swap) with
  | Success (instrs, _, _) => instrs
  | _ => nil
  end.
Compute instrs_swap.
Definition finfo_swap :=
  match (compile compile_ext_call fs_swap) with
  | Success (_, finfo, _) => finfo
  | _ => nil
  end.
Definition req_stack_size_swap :=
  match (compile compile_ext_call fs_swap) with
  | Success (_, _, req_stack_size) => req_stack_size
  | _ => 0
  end.
Definition fname_swap := "swap".
Definition f_rel_pos_swap := 0.
Definition post : list LogItem -> mem -> list Words32Naive.word -> Prop := fun _ _ _ => True.
Print ct_spec_of_swap.
Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_swap instrs_swap finfo_swap req_stack_size_swap fname_swap _ _ _ _).
Check compiler_correct_wp.

Lemma swap_ct :
  forall a_addr b_addr p_funcs stack_hi,
  exists finalTrace : list LeakageEvent,
  forall R m a b stack_lo ret_addr
                       Rdata Rexec (initial : RiscvMachine),
    Separation.sep (Separation.sep (Scalars.scalar a_addr a) (Scalars.scalar b_addr b)) R m ->
    req_stack_size_swap <= word.unsigned (word.sub stack_hi stack_lo) / SeparationLogic.bytes_per_word ->
    word.unsigned (word.sub stack_hi stack_lo) mod SeparationLogic.bytes_per_word = 0 ->
    getPc initial = word.add p_funcs (word.of_Z f_rel_pos_swap) ->
    map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    LowerPipeline.arg_regs_contain (getRegs initial) [a_addr; b_addr] ->
    LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_swap m Rdata Rexec initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         (exists (mH' : mem) (retvals : list Words32Naive.word),
           LowerPipeline.arg_regs_contain (getRegs final) retvals /\
             post (getLog final) mH' retvals /\
             map.only_differ (getRegs initial) reg_class.caller_saved (getRegs final) /\
             getPc final = ret_addr /\
             LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_swap mH' 
               Rdata Rexec final) /\
             final.(getTrace) = (finalTrace ++ initial.(getTrace))%list).
Proof.
  assert (spec := @swap_ok Words32Naive.word mem word_ok' mem_ok).
  cbv [ProgramLogic.program_logic_goal_for] in spec.
  specialize (spec nil). cbv [ct_spec_of_swap] in spec. destruct spec as [f spec].
  intros. Print compiler_correct_wp''. Unshelve.
  edestruct (@compiler_correct_wp'' _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_swap instrs_swap finfo_swap req_stack_size_swap stack_hi p_funcs fname_swap).
  { simpl. reflexivity. }
  { vm_compute. reflexivity. }
  exists x. intros.
  eapply H.
  { simpl. repeat constructor. tauto. }
  2: { eapply map.get_of_list_In_NoDup.
       { vm_compute. repeat constructor; eauto. }
       { vm_compute. left. reflexivity. } }
  2,3,4,5,6,7,9: eassumption.
  2: reflexivity.
  specialize (spec nil (getLog initial) m a_addr b_addr a b R H0). cbv [fs_swap fname_swap].
  eapply WeakestPreconditionProperties.Proper_call.
  2: eapply spec.
  cbv [Morphisms.pointwise_relation Basics.impl]. intros.
  split.
  2: cbv [post]; reflexivity.
  destruct H8 as [H8 [H9 H10] ]. subst. destruct H8 as [k'' [H8 H11] ]. subst. exists k''.
  split; eauto.
Qed.

Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_swap instrs_swap finfo_swap req_stack_size_swap fname_swap _ _ _ _).

Print Assumptions swap_ct.
(* Prints:

    Axioms:
        PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
        mem_ok : map.ok mem
        mem : map.map Words32Naive.word byte
        localsL_ok : map.ok localsL
        localsL : map.map Z Words32Naive.word
        FunctionalExtensionality.functional_extensionality_dep
          : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
            (forall x : A, f x = g x) -> f = g
        envH_ok : map.ok envH
        envH : map.map string (list string * list string * cmd)
        em : forall P : Prop, P \/ ~ P
        RVM : RiscvProgramWithLeakage
        PRParams : PrimitivesParams M RiscvMachine
        PR : MetricPrimitives PRParams
        MM : Monad M
        M : Type -> Type

 *)

Definition fs_io_function := &[,io_function;swap].
Definition instrs_io_function :=
  match (compile compile_ext_call fs_io_function) with
  | Success (instrs, _, _) => instrs
  | _ => nil
  end.
Compute instrs_swap.
Definition finfo_io_function :=
  match (compile compile_ext_call fs_io_function) with
  | Success (_, finfo, _) => finfo
  | _ => nil
  end.
Definition req_stack_size_io_function :=
  match (compile compile_ext_call fs_io_function) with
  | Success (_, _, req_stack_size) => req_stack_size
  | _ => 0
  end.
Definition fname_io_function := "io_function".
Definition f_rel_pos_io_function := 0.

Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_io_function instrs_io_function finfo_io_function req_stack_size_io_function fname_io_function _ _ _ _).

Print ct_spec_of_io_function.

Lemma io_function_ct :
  forall x p_funcs stack_hi,
  exists finalTrace : list LeakageEvent,
  forall R m y stack_lo ret_addr
                       Rdata Rexec (initial : RiscvMachine),
    (*Separation.sep (Separation.sep (Scalars.scalar a_addr a) (Scalars.scalar b_addr b)) R m ->*)
    req_stack_size_io_function <= word.unsigned (word.sub stack_hi stack_lo) / SeparationLogic.bytes_per_word ->
    word.unsigned (word.sub stack_hi stack_lo) mod SeparationLogic.bytes_per_word = 0 ->
    getPc initial = word.add p_funcs (word.of_Z f_rel_pos_io_function) ->
    map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    (*LowerPipeline.arg_regs_contain (getRegs initial) [a_addr; b_addr] ->*)
    LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_io_function m Rdata Rexec initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         (exists (mH' : mem) (retvals : list Words32Naive.word),
           LowerPipeline.arg_regs_contain (getRegs final) retvals /\
             post (getLog final) mH' retvals /\
             map.only_differ (getRegs initial) reg_class.caller_saved (getRegs final) /\
             getPc final = ret_addr /\
             LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_io_function mH' 
               Rdata Rexec final) /\
           (exists x' y',
               (final.(getLog) = [(map.empty, "MMIOREAD", [word.of_Z 0], (map.empty, [x']));
                                 (map.empty, "MMIOREAD", [word.of_Z 0], (map.empty, [y']))] ++
                                  initial.(getLog))%list /\
                 (x' = x ->
                  y' = y ->
                  R m /\ (final.(getTrace) = finalTrace ++ initial.(getTrace))%list))).
Proof.
  assert (spec := @io_function_ok Words32Naive.word mem word_ok' mem_ok).
  cbv [ProgramLogic.program_logic_goal_for] in spec.
  specialize (spec nil). cbv [ct_spec_of_io_function] in spec.
  intros.
  edestruct (@compiler_correct_wp'' _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_io_function instrs_io_function finfo_io_function req_stack_size_io_function stack_hi p_funcs fname_io_function).
  { simpl. reflexivity. }
  { vm_compute. reflexivity. }
  exists x0. intros. Print compiler_correct_wp''.
  eapply H.
  { simpl. repeat constructor. tauto. }
  2: { eapply map.get_of_list_In_NoDup.
       { vm_compute. repeat constructor; eauto. }
       { vm_compute. left. reflexivity. } }
  2,3,4,5,6,7,9: eassumption.
  2: reflexivity.
  specialize (spec nil (getLog initial) m a_addr b_addr a b R H0). cbv [fs_io_function fname_io_function].
  eapply WeakestPreconditionProperties.Proper_call.
  2: eapply spec.
  cbv [Morphisms.pointwise_relation Basics.impl]. intros.
  split.
  2: cbv [post]; reflexivity.
  destruct H8 as [H8 [H9 H10] ]. subst. destruct H8 as [k'' [H8 H11] ]. subst. exists k''.
  split; eauto.

(*
(* Not sure I can actually prove this. *)
Lemma a_trace_exists :
  forall initial next P,
  FlatToRiscvCommon.runsTo initial
    (fun final : RiscvMachine =>
       P final /\
         (exists (tL : list LeakageEvent) (F : nat),
             getTrace final = (tL ++ getTrace initial)%list /\
               (forall fuel : nat,
                   (F <= fuel)%nat ->
                   FlatToRiscvCommon.predictsLE (next fuel)
                     (rev tL)))) ->
  exists k',
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         P final /\
           getTrace final = k').
Proof. Abort.

Print FlatToRiscvDef.qLeakageEvent.
Fixpoint trace_of_predictor so_far next fuel :=
  match fuel with
  | O => nil
  | S fuel' =>
      match next fuel so_far with
      | Some (FlatToRiscvDef.qLE e) => e :: trace_of_predictor (app so_far (cons e nil)) next fuel'
      | Some (FlatToRiscvDef.qendLE) => []
      | None => []
      end
  end.

Notation predictsLE := FlatToRiscvCommon.predictsLE.
Print FlatToRiscvDef.qLeakageEvent.
Lemma predictsLE_end f l :
      predictsLE f l ->
      f l = Some FlatToRiscvDef.qendLE.
Proof.
  intros H. induction H.
  - rewrite H0. assumption.
  - assumption.
Qed.

Lemma trace_of_predictor_works' so_far next F k :
  (forall fuel,
    (F <= fuel)%nat ->
    predictsLE (next fuel) (so_far ++ k)) ->
  exists F',
    (forall fuel,
        (F' <= fuel)%nat ->
        k%list = trace_of_predictor so_far next fuel).
Proof.
  intros H. generalize dependent so_far. subst. induction k.
  - intros. exists (S F). intros. destruct fuel as [|fuel']; [blia|]. simpl.
    specialize (H (S fuel') ltac:(blia)). rewrite List.app_nil_r in H.
    apply predictsLE_end in H. rewrite H. reflexivity.
  - intros.
    specialize (IHk (so_far ++ [a])%list). rewrite <- app_assoc in IHk.
    specialize (IHk H). destruct IHk as [F' IHk]. 
    exists (S (F + F')). intros. destruct fuel as [|fuel']; [blia|].
    specialize (H (S fuel') ltac:(blia)). Search predictsLE.
    apply FlatToRiscvFunctions.predictLE_cons in H. simpl. rewrite H. simpl. f_equal.
    apply IHk. blia.
Qed.

Lemma trace_of_predictor_works next F k :
  (forall fuel,
    (F <= fuel)%nat ->
    predictsLE (next fuel) k) ->
  exists F',
    (forall fuel,
        (F' <= fuel)%nat ->
        k = trace_of_predictor [] next fuel).
Proof.
  intros. replace k with ([] ++ k)%list by reflexivity. eapply trace_of_predictor_works'.
  apply H.
Qed.

Require Import riscv.Utility.MonadT.

Lemma predictsLE_ext p1 p2 l :
  (forall x, p1 x = p2 x) ->
  predictsLE p1 l ->
  predictsLE p2 l.
Proof.
  intros H H0. induction H0.
  - econstructor.
    + rewrite <- H. assumption.
    + intros. rewrite <- H. auto.
    + assumption.
  - constructor. rewrite <- H. assumption.
Qed.

Lemma predictLE_unique p l1 l2 :
  predictsLE p l1 ->
  predictsLE p l2 ->
  l1 = l2.
Proof.
  intros. generalize dependent l2. generalize dependent p. induction l1.
  - intros. destruct l2; [reflexivity|]. remember [] as thing. destruct H; try congruence.
    destruct H0; try congruence. rewrite H0 in H. injection H as H.
    cbv [FlatToRiscvDef.quotLE] in H. congruence.
  - intros. destruct l2 eqn:E.
    + clear IHl1. remember [] as thing. destruct H; try congruence. destruct H0; try congruence.
      rewrite H0 in H. injection H as H.
      cbv [FlatToRiscvDef.quotLE] in H. congruence.
    + remember (a :: l1) as l1'. destruct H.
      -- destruct H0.
         ++ rewrite H0 in H. injection H as H. subst. f_equal. injection Heql1'. intros. subst.
            eapply IHl1.
            --- exact H2.
            --- eapply predictsLE_ext. 2: eassumption. intros. rewrite <- H3, H1. reflexivity.
         ++ rewrite H0 in H. injection H as H. cbv [FlatToRiscvDef.quotLE] in H. congruence.
      -- destruct H0; congruence.
Qed.

(* This should be easy to prove, though. *)
Lemma a_trace_sorta_exists :
  forall initial next P,
  FlatToRiscvCommon.runsTo initial
    (fun final : RiscvMachine =>
       P final /\
         (exists (tL : list LeakageEvent) (F : nat),
             getTrace final = (tL ++ getTrace initial)%list /\
               (forall fuel : nat,
                   (F <= fuel)%nat ->
                   FlatToRiscvCommon.predictsLE (next fuel)
                     (rev tL)))) ->
  exists finalTrace,
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         P final /\ exists F,
           forall fuel : nat,
             (F <= fuel)%nat ->
             getTrace final = finalTrace fuel).
Proof.
  intros. exists (fun fuel => (rev (trace_of_predictor nil next fuel) ++ getTrace initial)%list).
  cbv [FlatToRiscvCommon.runsTo]. eapply runsToNonDet.runsTo_weaken.
  1: eapply H. simpl. intros. destruct H0 as [H1 [tL [F [H2 H3] ] ] ].
  split; [assumption|]. assert (H3' := H3).
  apply trace_of_predictor_works in H3. destruct H3 as [F' H3].
  intros. simpl in H. exists F'. intros. rewrite H2. f_equal.
  rewrite <- (rev_involutive tL). f_equal. apply H3. apply H0.
Qed.

Require Import riscv.Platform.MetricSane.

Print FlatToRiscvCommon.runsTo.
Search runsToNonDet.runsTo.

Print runsToNonDet.runsTo.

Definition P : nat -> Prop := fun n => (n <= 5)%nat.

Check run1_sane. Check (run1 _).
Print mcomp_sane.
Lemma runsTo_sane :
  forall (st : RiscvMachine) (post : RiscvMachine -> Prop),
    valid_machine st ->
    FlatToRiscvCommon.runsTo st post ->
    (exists (st' : RiscvMachine), post st' /\ valid_machine st') /\
      FlatToRiscvCommon.runsTo st
        (fun (st' : RiscvMachine) =>
           (post st' /\ (exists diff : list LogItem, getLog st' = (diff ++ getLog st)%list)) /\
             valid_machine st').
Proof.
  intros. induction H0.
  - split.
    + exists initial. split; assumption.
    + constructor. split; [|assumption]. split; [assumption|]. exists nil. reflexivity.
  - assert (H3 := run1_sane RV32I). cbv [mcomp_sane] in H3.
    specialize (H3 initial (fun _ => midset) H H0).
    destruct H3 as [ [_ [midst [H3 H4] ] ] H5].
    split.
    + specialize (H2 midst H3 H4). destruct H2 as [H2 H2'].  exact H2.
    + Print runsToNonDet.runsTo. eapply runsToNonDet.runsToStep.
      -- exact H5.
      -- simpl. intros mid [ [H6 H7] H8]. specialize (H2 mid H6 H8).
         destruct H2 as [_ H2]. eapply runsToNonDet.runsTo_weaken.
         ++ exact H2.
         ++ simpl. intros final [ [H9 [diff H10] ] H11].
            split; [|assumption]. split; [assumption|]. rewrite H10.
            destruct H7 as [diff' H7]. rewrite H7. eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma last_step :
  forall
    (initial : RiscvMachine)
    (P : RiscvMachine -> Prop)
    (finalTrace : nat -> list LeakageEvent),

    valid_machine initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         P final /\
           exists F,
           forall fuel : nat,
             (F <= fuel)%nat ->
             getTrace final = finalTrace fuel) ->
    
    exists (n : nat),
      FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         P final /\
           getTrace final = finalTrace n).
Proof.
  intros. cbv [FlatToRiscvCommon.runsTo] in H0. 
  assert (H1 := runsTo_sane).
  specialize (H1 _ _ H H0). destruct H1 as [H1 _]. destruct H1 as [st' [ [H1 H2] H3] ].
  destruct H2 as [F H2].
  exists F. eapply runsToNonDet.runsTo_weaken.
  - exact H0.
  - clear H H0. simpl. intros final [H4 H5]. split; [assumption|].
    destruct H5 as [F' H5]. specialize (H5 (F' + F)%nat ltac:(blia)).
    assert (H2' := H2 F ltac:(blia)).
    specialize (H2 (F' + F)%nat ltac:(blia)).
    rewrite <- H2'. rewrite H2. apply H5.
Qed.

Check a_trace_sorta_exists.
Check last_step.

Lemma predictor_thing_correct :
  forall (initial : RiscvMachine)
         (next : nat -> list LeakageEvent -> option FlatToRiscvDef.qLeakageEvent)
         (P : RiscvMachine -> Prop),
    valid_machine initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         P final /\
           (exists (tL : list LeakageEvent) (F : nat),
               getTrace final = (tL ++ getTrace initial)%list /\
                 (forall fuel : nat, (F <= fuel)%nat -> predictsLE (next fuel) (rev tL)))) ->
    exists finalTrace,
      FlatToRiscvCommon.runsTo initial
        (fun final : RiscvMachine => P final /\ getTrace final = finalTrace).
Proof.
  intros initial next P H1 H2.
  apply a_trace_sorta_exists in H2.
  destruct H2 as [finalTrace H2].
  apply last_step in H2; try assumption.
  destruct H2 as [n H2].
  exists (finalTrace n). assumption.
Qed.*)
