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
Definition fs := &[,swap].
Check compiler_correct_wp.
Print compiler_correct_wp.
Print ExtSpec.
Context {mem : map.map Words32Naive.word byte}.
Context {mem_ok : map.ok mem}.
Context {locals : map.map Z Words32Naive.word}.
Context {locals_ok : map.ok locals}.
Context {env : map.map string (list Z * list Z * FlatImp.stmt Z)}.
Context {M : Type -> Type} {MM : Monad M}.
Context {RVM: RiscvProgramWithLeakage}.
Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
Context {PR: MetricPrimitives PRParams}.

Definition leak_ext_call : list LeakageEvent := nil.
#[local] Instance ext_spec: ExtSpec :=
  fun t mGive action argvals post =>
    False. Print FlatToRiscvCommon.compiles_FlatToRiscv_correctly.
Lemma ext_spec_ok : ext_spec.ok ext_spec.
Proof.
  constructor; intros; cbv [ext_spec] in *; try destruct H.
  cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl].
  auto.
Qed.
Check (@FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I _ _ _ _ _ compile_ext_call
         leak_ext_call _ _ _ _ _ _ _ _ compile_ext_call).
Check @compiler_correct_wp.
Check (@PrimitivesParams _ _ _ _ _ M MetricRiscvMachine).
Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ ext_spec_ok _ _ _ _ _).
Check NaiveRiscvWordProperties.naive_word_riscv_ok.
Lemma word_ok : RiscvWordProperties.word.riscv_ok Words32Naive.word.
Proof.
  cbv [Words32Naive.word]. replace 32 with (2 ^ BinInt.Z.of_nat 5) by reflexivity.
  apply NaiveRiscvWordProperties.naive_word_riscv_ok.
Qed.


Lemma compile_ext_call_works :
  (forall (resvars : list Z) (extcall : string) (argvars : list Z),
        @FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I 32 Bitwidth32.BW32
          Words32Naive.word locals (SortedListString.map Z) compile_ext_call leak_ext_call mem
          (SortedListString.map (list Z * list Z * FlatImp.stmt Z)) M MM RVM PRParams ext_spec
          RV32I_bitwidth compile_ext_call (@FlatImp.SInteract Z resvars extcall argvars)).
Proof.
  intros. cbv [FlatToRiscvCommon.compiles_FlatToRiscv_correctly]. intros. exfalso. clear -H.
  inversion H. subst. cbv [ext_spec] in *. assumption.
Qed.

Lemma compile_ext_call_length :
  (forall (stackoffset : Z) (posmap1 posmap2 : SortedListString.map Z) 
          (c : FlatImp.stmt Z) (pos1 pos2 : Z),
        @Datatypes.length Instruction (compile_ext_call posmap1 pos1 stackoffset c) =
          @Datatypes.length Instruction (compile_ext_call posmap2 pos2 stackoffset c)).
Proof.
  intros. cbv [compile_ext_call]. reflexivity. Qed.
Compute (compile compile_ext_call fs).
Definition instrs :=
  match (compile compile_ext_call fs) with
  | Success (instrs, _, _) => instrs
  | _ => nil
  end.
Definition finfo :=
  match (compile compile_ext_call fs) with
  | Success (_, finfo, _) => finfo
  | _ => nil
  end.
Definition req_stack_size :=
  match (compile compile_ext_call fs) with
  | Success (_, _, req_stack_size) => req_stack_size
  | _ => 0
  end.
Definition fname := "swap".
Definition f_rel_pos := 0.
Definition post : list LogItem -> mem -> list Words32Naive.word -> Prop := fun _ _ _ => True.
Print ct_spec_of_swap.
Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_works compile_ext_call_length fs instrs finfo req_stack_size fname _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Check compiler_correct_wp.

Lemma swap_ct : forall R m a_addr b_addr a b stack_lo stack_hi ret_addr p_funcs
                       Rdata Rexec (initial : RiscvMachine),
    Separation.sep (Separation.sep (Scalars.scalar a_addr a) (Scalars.scalar b_addr b)) R m ->
    req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / SeparationLogic.bytes_per_word ->
    word.unsigned (word.sub stack_hi stack_lo) mod SeparationLogic.bytes_per_word = 0 ->
    getPc initial = word.add p_funcs (word.of_Z f_rel_pos) ->
    map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    LowerPipeline.arg_regs_contain (getRegs initial) [a_addr; b_addr] ->
    LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs m Rdata Rexec initial ->
    exists
         next : Words32Naive.word * Z * Words32Naive.word ->
                nat -> list LeakageEvent -> option FlatToRiscvDef.qLeakageEvent,
         FlatToRiscvCommon.runsTo initial
           (fun final : RiscvMachine =>
            exists (mH' : mem) (retvals : list Words32Naive.word),
              LowerPipeline.arg_regs_contain (getRegs final) retvals /\
              post (getLog final) mH' retvals /\
              map.only_differ (getRegs initial) reg_class.caller_saved (getRegs final) /\
              getPc final = ret_addr /\
              LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs mH' 
                Rdata Rexec final /\
              (exists (tL : list LeakageEvent) (F : nat),
                 getTrace final = (tL ++ getTrace initial)%list /\
                 (forall fuel : nat,
                  (F <= fuel)%nat ->
                  FlatToRiscvCommon.predictsLE (next (p_funcs, f_rel_pos, stack_hi) fuel)
                    (rev tL)))).
Proof.
  intros.
  assert (spec := swap_ok). cbv [ProgramLogic.program_logic_goal_for] in spec.
  specialize (spec nil). cbv [ct_spec_of_swap] in spec. destruct spec as [f spec].
  
  eapply (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_works compile_ext_call_length fs instrs finfo req_stack_size fname).
  { reflexivity. }
  { simpl. repeat constructor. intros H'. destruct H'. }
  { reflexivity. }
  2: { Search (map.get (map.of_list _)). eapply map.get_of_list_In_NoDup.
       { vm_compute. repeat constructor; eauto. }
       { vm_compute. left. reflexivity. } }
  Search FlatToRiscvCommon.runsTo. 2,3,4,5,6,7,9: eassumption.
  2: reflexivity. Print ct_spec_of_swap. Print ct_spec_of_swap. Search ct_spec_of_swap.
  Check swap_ok. Print ProgramLogic.program_logic_goal_for.
  specialize (spec nil (getLog initial) m a_addr b_addr a b R H). cbv [fs fname]. Search WeakestPrecondition.call. eapply WeakestPreconditionProperties.Proper_call. 2: eapply spec.
  cbv [Morphisms.pointwise_relation Basics.impl]. intros.
  split.
  { cbv [post]. apply I. }
  { destruct H7 as [H7 [H8 H9] ]. subst. destruct H7 as [k'' [H7 H10] ]. exists k''.
    apply predictor_works in H7. subst. instantiate (1 := fun _ _ => (predictor (WeakestPrecondition.appl a_addr (WeakestPrecondition.appl b_addr f)))). exists O. split; [reflexivity|].
    intros. assumption.
    Unshelve.
    { apply ext_spec_ok. } }
Qed.
