Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricLogging.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.MetricLogging.
Require Import compiler.ExprImp.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.FlatImp.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Import riscv.Spec.Decode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Spilling.
Require Import compiler.RegAlloc.
Require Import compiler.RiscvEventLoop.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Export coqutil.Word.SimplWordExpr.
Require Export compiler.Registers.
Require Import compiler.ForeverSafe.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.LowerPipeline.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.UseImmediateDef.
Require Import compiler.UseImmediate.
Import Utility.

Section WithWordAndMem.
  Context {width: Z} {BW: Bitwidth width} {word: Interface.word width} {mem : map.map word byte}.

  Record Lang := {
      Program: Type;
      Valid: Program -> Prop;
      Settings: Type;
      Event: Type;
      QEvent: Type;
      predicts: (list Event -> QEvent) -> list Event -> Prop;
      Call(p: Program)(s: Settings)(funcname: string)
        (k: list Event)(t: io_trace)(m: mem)(argvals: list word)
        (post: list Event -> io_trace -> mem -> list word -> Prop): Prop;
  }.

  Record phase_correct{L1 L2: Lang}
    {compile: L1.(Program) -> result L2.(Program)}: Prop :=
  {
    phase_preserves_valid: forall p1 p2,
        compile p1 = Success p2 ->
        L1.(Valid) p1 ->
        L2.(Valid) p2;
    phase_preserves_post: forall p1 p2,
        L1.(Valid) p1 ->
        compile p1 = Success p2 ->
        forall s1 s2 fname,
        exists f,
        forall k1 k2 t m argvals post,
          L1.(Call) p1 s1 fname k1 t m argvals post ->
          L2.(Call) p2 s2 fname k2 t m argvals
               (fun k2' t' m' retvals =>
                  exists k1'' k2'',
                    post (k1'' ++ k1) t' m' retvals /\
                      k2' = k2'' ++ k2 /\
                      forall next,
                        L1.(predicts) next (rev k1'') ->
                        exists F,
                        forall fuel,
                          (F <= fuel)%nat ->
                          L2.(predicts) (f fuel next) (rev k2''));
  }.

  Arguments phase_correct : clear implicits.

  Definition compose_phases{A B C: Type}(phase1: A -> result B)(phase2: B -> result C):
    A -> result C :=
    fun a => match phase1 a with
             | Success b => phase2 b
             | Failure e => Failure e
             end.

  Lemma compose_phases_correct{L1 L2 L3: Lang}
        {compile12: L1.(Program) -> result L2.(Program)}
        {compile23: L2.(Program) -> result L3.(Program)}:
    phase_correct L1 L2 compile12 ->
    phase_correct L2 L3 compile23 ->
    phase_correct L1 L3 (compose_phases compile12 compile23).
  Proof.
    unfold compose_phases.
    intros [V12 C12] [V23 C23].
    split; intros; fwd; eauto.
    specialize (V12 p1 a E H).
    specialize (C23 a p2 V12 H0 fname).
    specialize (C12 p1 a H E fname next). destruct C12 as [next' C12].
    specialize (C23 next'). destruct C23 as [next'' C23].
    eauto.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            {ext_spec: ExtSpec}
            {leak_ext: LeakExt}
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    (* for riscv phase: *)
    Context {Registers: map.map Z word}.
    Context {M: Type -> Type}.
    Context {MM: Monad M}.
    Context {RVM: RiscvProgramWithLeakage}.
    Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
    Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
    Context {Registers_ok: map.ok Registers}.
    Context {PR: MetricPrimitives PRParams}.
    Context {iset: InstructionSet}.
    Context {BWM: bitwidth_iset width iset}.
    Context (compile_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z ->
                                list Instruction).
    Context (leak_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z ->
                             list word -> list LeakageEvent).
    Context (compile_ext_call_correct: forall resvars extcall argvars,
                compiles_FlatToRiscv_correctly compile_ext_call leak_ext_call compile_ext_call
                                               (FlatImp.SInteract resvars extcall argvars)).
    Context (compile_ext_call_length_ignores_positions:
               forall stackoffset posmap1 posmap2 c pos1 pos2,
                List.length (compile_ext_call posmap1 pos1 stackoffset c) =
                List.length (compile_ext_call posmap2 pos2 stackoffset c)).

    Definition is5BitImmediate(x: Z) : bool :=
      andb (Z.leb 0 x) (Z.ltb x 32).
    Definition is12BitImmediate(x: Z) : bool :=
      andb (Z.leb (-2048) x) (Z.ltb x 2048).

    Definition locals_based_call_spec{Var Cmd: Type}{locals: map.map Var word}
               (Exec: string_keyed_map (list Var * list Var * Cmd) ->
                      Cmd -> trace -> io_trace -> mem -> locals -> MetricLog ->
                      (trace -> io_trace -> mem -> locals -> MetricLog -> Prop) -> Prop)
               (e: string_keyed_map (list Var * list Var * Cmd))(f: string)
               (next: unit -> nat -> trace -> option qevent)
               (k: trace)(t: io_trace)(m: mem)(argvals: list word)
               (post: io_trace -> mem -> list word -> Prop): Prop :=
      exists argnames retnames fbody l,
        map.get e f = Some (argnames, retnames, fbody) /\
        map.of_list_zip argnames argvals = Some l /\
        forall mc, Exec e fbody k t m l mc (fun k' t' m' l' mc' =>
                       exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                         post t' m' retvals /\
                                         exists k'' F,
                                           k' = k'' ++ k /\
                                             forall fuel,
                                               le F fuel ->
                                               predicts (next tt fuel) (rev k'')).

    Definition ParamsNoDup{Var: Type}: (list Var * list Var * FlatImp.stmt Var) -> Prop :=
      fun '(argnames, retnames, body) => NoDup argnames /\ NoDup retnames.

    Definition SrcLang: Lang := {|
      Program := string_keyed_map (list string * list string * Syntax.cmd);
      Valid := map.forall_values ExprImp.valid_fun;
      Call := locals_based_call_spec Semantics.exec;
    |}.
    (* |                 *)
    (* | FlattenExpr     *)
    (* V                 *)
    Definition FlatWithStrVars: Lang := {|
      Program := string_keyed_map (list string * list string * FlatImp.stmt string);
      Valid := map.forall_values ParamsNoDup;
      Call := locals_based_call_spec FlatImp.exec;
    |}.

    (* |                 *)
    (* | UseImmediate    *)
    (* V                 *)
    (* FlatWithStrVars   *)

    (* |                 *)
    (* | RegAlloc        *)
    (* V                 *)
    Definition FlatWithZVars: Lang := {|
      Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      Valid := map.forall_values ParamsNoDup;
      Call := locals_based_call_spec FlatImp.exec;
    |}.
    (* |                 *)
    (* | Spilling        *)
    (* V                 *)
    Definition FlatWithRegs: Lang := {|
      Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      Valid := map.forall_values FlatToRiscvDef.valid_FlatImp_fun;
      Call := locals_based_call_spec FlatImp.exec;
    |}.
    (* |                 *)
    (* | FlatToRiscv     *)
    (* V                 *) Print riscv_call. Print Lang. Check string_keyed_map Z.
    Definition RiscvLang: Lang := {|
      Program :=
        list Instruction *      (* <- code of all functions concatenated       *)
        string_keyed_map Z *    (* <- position (offset) for each function      *)
        Z;                      (* <- required stack space in XLEN-bit words   *)
      (* bounds in instructions are checked by `ptsto_instr` *)
      Valid '(insts, finfo, req_stack_size) := True;
      Call := (fun p fname next =>
                 riscv_call p fname next);
    |}.

    Lemma flatten_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        flatten_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold flatten_functions. intros.
      eapply map.try_map_values_bw in H0. 2: eassumption.
      unfold flatten_function in *. fwd.
      eapply H. eassumption.
    Qed.

    Lemma flattening_correct: phase_correct SrcLang FlatWithStrVars flatten_functions.
    Proof.
      unfold SrcLang, FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup.
        intros. destruct v as ((argnames & retnames) & body).
        eapply flatten_functions_NoDup; try eassumption.
        unfold valid_fun in *.
        intros. specialize H0 with (1 := H2). simpl in H0. eapply H0.
      }
      unfold locals_based_call_spec. intros. eexists. intros. fwd.
      pose proof H0 as GF.
      unfold flatten_functions in GF.
      eapply map.try_map_values_fw in GF. 2: eassumption.
      unfold flatten_function in GF. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux with (mcH := mc).
        + eassumption.
        + eauto.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k0 A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k0 A.
          rewrite map.get_empty. destr (map.get l k0). 2: reflexivity. exfalso.
          unfold map.of_list_zip in H1p1.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H1p1 E) as [G | G].
          2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. fwd. eauto 8 using map.getmany_of_list_extends.
       Qed.

    Lemma useimmediate_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        (useimmediate_functions is5BitImmediate is12BitImmediate) funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold useimmediate_functions. intros.
      eapply map.try_map_values_bw in H0.
      2: { eassumption.  }
      unfold useimmediate_function in *.
      fwd.
      eapply H.
      eassumption.
    Qed.

    Lemma useimmediate_correct: phase_correct FlatWithStrVars FlatWithStrVars (useimmediate_functions is5BitImmediate is12BitImmediate).
    Proof.
      unfold FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as  ((argnames & retnames) & body).
        eapply useimmediate_functions_NoDup; try eassumption.
        intros. specialize H0 with (1 := H2).
        simpl in H0. assumption.
      }

      unfold locals_based_call_spec. intros. eexists. intros. fwd.
      pose proof H0 as GI.
      unfold  useimmediate_functions in GI.
      eapply map.try_map_values_fw in GI. 2: eassumption.
      unfold useimmediate_function in GI. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply exec.weaken.
      - eapply useImmediate_correct_aux.
        all: eauto.
      - simpl. eauto 10.
    Qed.

    Lemma regalloc_functions_NoDup: forall funs funs',
        regalloc_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold regalloc_functions, check_funcs. intros.
      fwd.
      eapply map.try_map_values_bw in E. 2: eassumption.
      fwd.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func, assert in *.
      destruct v1 as ((args1 & rets1) & body1). fwd.
      rewrite <- E1, <- E4.
      split; apply List.NoDup_dedup.
    Qed.

    Lemma regalloc_correct: phase_correct FlatWithStrVars FlatWithZVars regalloc_functions.
    Proof.
      unfold FlatWithStrVars, FlatWithZVars. split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as ((argnames & retnames) & body).
        eapply regalloc_functions_NoDup; eassumption.
      }
      unfold locals_based_call_spec.
      intros. eexists. intros. fwd.
      pose proof H0 as GR.
      unfold regalloc_functions in GR.
      fwd. rename E into GR.
      eapply map.try_map_values_fw in GR. 2: eassumption.
      fwd. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. fwd.

      rename l0 into argregs, l1 into retregs.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argregs argvals = Some l'). {
        eapply map.sameLength_putmany_of_list. congruence.
      }
      fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; eauto.
        eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
        1: eapply states_compat_empty.
        rewrite H1 in P'. inversion P'. exact Cp.
      - simpl. intros. fwd. eexists. split. 2: split; [eassumption|].
        1: eauto using states_compat_getmany. eauto.
    Qed.

    Ltac debool :=
      repeat match goal with
             | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H
             | H: _ /\ _ |- _ => destruct H as [? H]
             | H: _ <? _ = true |- _ => eapply Z.ltb_lt in H
             | H: (_ <=? _)%nat = true |- _ => eapply Nat.leb_le in H
             end.

    Lemma spilling_preserves_valid: forall p1 p2 : string_keyed_map (list Z * list Z * stmt Z),
        spill_functions p1 = Success p2 ->
        map.forall_values ParamsNoDup p1 ->
        map.forall_values FlatToRiscvDef.valid_FlatImp_fun p2.
    Proof.
      unfold spill_functions, map.forall_values. intros.
      eapply map.try_map_values_bw in H. 2: eassumption.
      unfold spill_fun in H. fwd.
      unfold FlatToRiscvDef.valid_FlatImp_fun, FlatToRiscvDef.valid_FlatImp_var,
      FlatToRiscvDef.valid_FlatImp_vars,
      FlatToRiscvDef.valid_FlatImp_var, fp in *.
      debool.
      ssplit.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - cbn. ssplit.
        + blia.
        + blia.
        + eapply set_vars_to_reg_range_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
        + eapply spill_stmt_valid_vars. 1: reflexivity.
          unfold valid_vars_src.
          eapply max_var_sound.
          eapply FlatImp.forallb_vars_stmt_correct.
          2: eassumption.
          unfold is_valid_src_var.
          intros; rewrite ?Bool.andb_true_iff, ?Z.ltb_lt; unfold fp; blia.
        + eapply set_reg_range_to_vars_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
      - cbn. ssplit.
        + apply set_vars_to_reg_range_uses_standard_arg_regs.
        + apply spill_stmt_uses_standard_arg_regs.
        + apply set_reg_range_to_vars_uses_standard_arg_regs.
    Qed.

    Lemma spilling_correct: phase_correct FlatWithZVars FlatWithRegs spill_functions.
    Proof.
      unfold FlatWithZVars, FlatWithRegs. split; cbn.
      1: exact spilling_preserves_valid.
      unfold locals_based_call_spec. intros.
      Check snext_fun.
      Check (match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end).
      exists (fun _ fuel => (snext_fun p1 fuel (next tt fuel) [] (match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end))).
      intros. fwd.
      pose proof H0 as GL.
      unfold spill_functions in GL.
      eapply map.try_map_values_fw in GL. 2: eassumption.
      destruct GL as (((argnames2 & retnames2) & fbody2) & Sp & G2).
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argnames2 argvals = Some l'). {
        eapply map.sameLength_putmany_of_list.
        unfold spill_fun in Sp. fwd.
        rewrite !List.firstn_length.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
        blia.
      }
      fwd.
      eexists argnames2, retnames2, fbody2, l'.
      split. 1: exact G2. split. 1: eassumption.
      intros. eapply exec.weaken. 1: eapply spill_fun_correct; try eassumption.
      { unfold call_spec. intros * E. rewrite E in *. fwd. eauto. }
      simpl. intros. fwd. exists retvals. split; [assumption|]. split; [assumption|].
      do 2 eexists. split; [reflexivity|]. intros. eauto.
    Qed.

    Lemma riscv_phase_correct: phase_correct FlatWithRegs RiscvLang (riscvPhase compile_ext_call).
    Proof.
      unfold FlatWithRegs, RiscvLang.
      split; cbn.
      - intros p1 ((? & finfo) & ?). intros. exact I.
      - intros. assert (E: (exists x, map.get p1 fname = Some x) -> map.get p1 fname = Some (match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end)).
        + intros. destruct H1 as [x H1]. destruct (map.get p1 fname); congruence.
        + destruct (match map.get p1 fname with
                    | Some finfo => finfo
                    | None => ([], [], SSkip)
                    end) as [ [argnames0 retnames0] fbody0 ].
        (*cbv [locals_based_call_spec] in H1.
        fwd.*) destruct p2 as [ [instrs finfo] req_stack_size]. Check flat_to_riscv_correct. eexists. intros.
        eapply flat_to_riscv_correct; eauto.
        cbv [locals_based_call_spec] in H1. fwd.
        exists l.
        assert (H1p0': map.get p1 fname = Some (argnames0, retnames0, fbody0)).
        { eapply E. eexists. apply H1p0. }
        rewrite H1p0 in H1p0'. injection H1p0'. intros. subst. clear H1p0'.
        eauto.
    Qed.

    Definition composed_compile:
      string_keyed_map (list string * list string * cmd) ->
      result (list Instruction * string_keyed_map Z * Z) :=
      (compose_phases flatten_functions
      (compose_phases (useimmediate_functions is5BitImmediate is12BitImmediate)
      (compose_phases regalloc_functions
      (compose_phases spill_functions
                      (riscvPhase compile_ext_call))))).

    Lemma composed_compiler_correct: phase_correct SrcLang RiscvLang composed_compile.
    Proof.
      unfold composed_compile.
      exact (compose_phases_correct flattening_correct
            (compose_phases_correct useimmediate_correct
            (compose_phases_correct regalloc_correct
            (compose_phases_correct spilling_correct
                                    riscv_phase_correct)))).
    Qed.
    Check composed_compiler_correct.
    Print phase_correct.

    Definition compile(funs: list (string * (list string * list string * cmd))):
      result (list Instruction * list (string * Z) * Z) :=
      match composed_compile (map.of_list funs) with
      | Success (insts, pos, space) => Success (insts, map.tuples pos, space)
      | Failure e => Failure e
      end.

    Definition valid_src_fun: (string * (list string * list string * cmd)) -> bool :=
      fun '(name, (args, rets, body)) =>
        andb (List.list_eqb String.eqb (List.dedup String.eqb args) args)
             (List.list_eqb String.eqb (List.dedup String.eqb rets) rets).

    Lemma valid_src_fun_correct: forall name f,
        valid_src_fun (name, f) = true -> ExprImp.valid_fun f.
    Proof.
      unfold valid_src_fun, valid_fun. intros. destruct f as ((args & rets) & body).
      fwd. split.
      - rewrite <- Hp0. apply List.NoDup_dedup.
      - rewrite <- Hp1. apply List.NoDup_dedup.
    Qed.

    Definition valid_src_funs: list (string * (list string * list string * cmd)) -> bool :=
      List.forallb valid_src_fun.

    Lemma valid_src_funs_correct fs:
        valid_src_funs fs = true ->
        ExprImp.valid_funs (map.of_list fs).
    Proof.
      unfold valid_funs. induction fs; intros.
      - simpl in H0. rewrite map.get_empty in H0. discriminate.
      - destruct a as (name & body). simpl in H0. rewrite map.get_put_dec in H0. fwd.
        destruct_one_match_hyp.
        + fwd. eapply valid_src_fun_correct. eassumption.
        + eapply IHfs; eassumption.
    Qed.

    (* restate composed_compiler_correct by unfolding definitions used to compose phases *)
    Lemma compiler_correct: forall
        (* input of compilation: *)
        (functions: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string),
        valid_src_funs functions = true ->
        compile functions = Success (instrs, finfo, req_stack_size) ->
        forall next, exists next',
        forall
        (* high-level initial state & post on final state: *)
        (k: trace) (t: io_trace) (mH: mem) (argvals: list word) (post: io_trace -> mem -> list word -> Prop),
        (exists (argnames retnames: list string) (fbody: cmd) l,
            map.get (map.of_list functions) fname = Some (argnames, retnames, fbody) /\
            map.of_list_zip argnames argvals = Some l /\
            forall mc,
              Semantics.exec (map.of_list functions) fbody k t mH l mc
                (fun k' t' m' l' mc' => exists retvals: list word,
                     map.getmany_of_list l' retnames = Some retvals /\
                       post t' m' retvals /\
                       exists k'' F,
                         k' = k'' ++ k /\
                           forall fuel,
                             le F fuel ->
                             predicts (next tt fuel) (rev k''))) ->
        exists (f_rel_pos: Z),
          map.get (map.of_list finfo) fname = Some f_rel_pos /\
          forall (* low-level machine on which we're going to run the compiled program: *)
                 (initial: MetricRiscvMachine)
                 (* ghost vars that help describe the low-level machine: *)
                 (stack_lo stack_hi: word) (ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop),
            req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
            word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
            initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
            map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
            word.unsigned ret_addr mod 4 = 0 ->
            arg_regs_contain initial.(getRegs) argvals ->
            initial.(getLog) = t ->
            machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
            runsTo initial (fun final : MetricRiscvMachine =>
              (exists mH' retvals,
                arg_regs_contain (getRegs final) retvals /\
                post final.(getLog) mH' retvals /\
                map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
                final.(getPc) = ret_addr /\
                  machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final) /\
              exists tL F,
              final.(getTrace) = tL ++ initial.(getTrace) /\
                forall fuel,
                  le F fuel ->
                  predictsLE (next' (p_funcs, f_rel_pos, stack_hi) fuel) (rev tL)).
    Proof.
      intros.
      pose proof (phase_preserves_post composed_compiler_correct) as C.
      unfold Call, SrcLang, RiscvLang, locals_based_call_spec, riscv_call in C.
      eapply valid_src_funs_correct in H.
      specialize C with (1 := H).
      assert (composed_compile (map.of_list functions) =
                Success (instrs, map.of_list finfo, req_stack_size)) as H0'. {
        clear -H0 string_keyed_map_ok. unfold compile in H0. fwd.
        rewrite map.of_list_tuples. reflexivity.
      }
      specialize C with (1 := H0').
      specialize (C fname next).
      cbv iota in C.
      fwd. exists next'. intuition eauto 20.
      specialize C with (1 := H1). clear H1. fwd. exists f_rel_pos. intuition eauto 10.
    Qed.

    Definition instrencode(p: list Instruction): list byte :=
      List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

    Ltac hyp p :=
      multimatch goal with
      | H: context[p] |- _ => H
      end.

    (* combines the above theorem with WeakestPrecondition soundness,
       and makes `map.get (map.of_list finfo) fname` a hyp rather than conclusion because
       in concrete instantiations, users need to lookup that position themselves anyways *)
    Check WeakestPrecondition.call.
    Lemma compiler_correct_wp: forall
        (* input of compilation: *)
        (fs: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string) next (f_rel_pos: Z),
        valid_src_funs fs = true ->
        compile fs = Success (instrs, finfo, req_stack_size) ->
        exists next', forall
        (* high-level initial state & post on final state: *)
        (k: trace) (t: io_trace) (mH: mem) (argvals: list word) (post: io_trace -> mem -> list word -> Prop)
        (* ghost vars that help describe the low-level machine: *)
        (stack_lo stack_hi ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop)
        (* low-level machine on which we're going to run the compiled program: *)
        (initial: MetricRiscvMachine),
        NoDup (map fst fs) ->
        WeakestPrecondition.call fs fname k t mH argvals
          (fun k' t' m' rets =>
             post t' m' rets /\
               exists k'' F,
                 k' = k'' ++ k /\
                   forall fuel,
                     le F fuel ->
                     predicts (next tt fuel) (rev k'')) ->
        map.get (map.of_list finfo) fname = Some f_rel_pos ->
        req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
        word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
        initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
        map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
        word.unsigned ret_addr mod 4 = 0 ->
        arg_regs_contain initial.(getRegs) argvals ->
        initial.(getLog) = t ->
        machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
        runsTo initial (fun final : MetricRiscvMachine =>
          (exists mH' retvals,
            arg_regs_contain (getRegs final) retvals /\
            post final.(getLog) mH' retvals /\
            map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
            final.(getPc) = ret_addr /\
              machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final) /\
              exists tL F,
                final.(getTrace) = tL ++ initial.(getTrace) /\
                  forall fuel,
                    le F fuel ->
                    predictsLE (next' (p_funcs, f_rel_pos, stack_hi) fuel) (rev tL)).
    Proof.
      intros.
      destruct (compiler_correct fs instrs finfo req_stack_size fname H H0 next) as [next' compiler_correct'].
      exists next'. intros.
      let H := hyp WeakestPrecondition.call in rename H into WP.
      eapply WeakestPreconditionProperties.sound_call' in WP.
      2: { eapply map.all_gets_from_map_of_NoDup_list; assumption. }
      fwd.
      edestruct compiler_correct' as (f_rel_pos' & G & C);
        try eassumption.
      - intros.
        unfold map.of_list_zip in *. eauto 10.
      - fwd. rewrite H3 in G. injection G as G. subst.
        eapply C; clear C; try assumption; try congruence.
    Qed.

    
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
  forall next,
  exists finalTrace,
  forall initial P,
  FlatToRiscvCommon.runsTo initial
    (fun final : MetricRiscvMachine =>
       P final /\
         (exists (tL : list LeakageEvent) (F : nat),
             getTrace final = (tL ++ getTrace initial)%list /\
               (forall fuel : nat,
                   (F <= fuel)%nat ->
                   FlatToRiscvCommon.predictsLE (next fuel)
                     (rev tL)))) ->
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\ exists F,
           forall fuel : nat,
             (F <= fuel)%nat ->
             getTrace final = finalTrace fuel ++ getTrace initial).
Proof.
  intros. exists (fun fuel => (rev (trace_of_predictor nil next fuel))%list).
  intros.
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
  forall (st : MetricRiscvMachine) (post : MetricRiscvMachine -> Prop),
    valid_machine st ->
    FlatToRiscvCommon.runsTo st post ->
    (exists (st' : MetricRiscvMachine), post st' /\ valid_machine st') /\
      FlatToRiscvCommon.runsTo st
        (fun (st' : MetricRiscvMachine) =>
           (post st' /\ (exists diff : list LogItem, getLog st' = (diff ++ getLog st)%list)) /\
             valid_machine st').
Proof.
  intros. induction H0.
  - split.
    + exists initial. split; assumption.
    + constructor. split; [|assumption]. split; [assumption|]. exists nil. reflexivity.
  - assert (H3 := run1_sane iset). cbv [mcomp_sane] in H3.
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

Lemma last_step_useless_version :
  forall
    (finalTrace : nat -> list LeakageEvent)
    (initial : MetricRiscvMachine)
    (P : MetricRiscvMachine -> Prop),
    valid_machine initial ->
    
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\
           exists F,
           forall fuel : nat,
             (F <= fuel)%nat ->
             getTrace final = finalTrace fuel ++ getTrace initial) ->

    exists n,
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\
           getTrace final = finalTrace n ++ getTrace initial).
Proof. Abort.

Axiom em : forall P, P \/ ~P. 

Lemma last_step :
  forall (finalTrace : nat -> list LeakageEvent),
    
  exists (n : nat),
  forall (initial : MetricRiscvMachine)
         (P : MetricRiscvMachine -> Prop),
    valid_machine initial ->
    
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\
           exists F,
           forall fuel : nat,
             (F <= fuel)%nat ->
             getTrace final = finalTrace fuel ++ getTrace initial) ->
    
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\
           getTrace final = finalTrace n ++ getTrace initial).
Proof.
  intros finalTrace.
  assert (H := em (exists F, forall fuel, (F <= fuel)%nat -> finalTrace fuel = finalTrace F)).
  destruct H as [H|H].
  - destruct H as [F H]. exists F. intros. eapply runsToNonDet.runsTo_weaken.
    + eassumption.
    + simpl. intros final [H2 [F' H3] ]. split; [assumption|].
      specialize (H (F + F')%nat ltac:(blia)). specialize (H3 (F + F')%nat ltac:(blia)).
      rewrite <- H. apply H3.
  - exists O. intros. eapply runsToNonDet.runsTo_weaken.
    + eassumption.
    + simpl. intros. destruct H2 as [_ H2]. exfalso. apply H. destruct H2 as [F H2].
      exists F. intros. assert (H4 := H2 F ltac:(blia)). assert (H5 := H2 fuel ltac:(blia)).
      rewrite H4 in H5. Search (_ ++ _ = _ ++ _ -> _ = _). apply app_inv_tail in H5. symmetry.
      assumption.
Qed.

Check a_trace_sorta_exists.
Check last_step.

Lemma predictor_thing_correct :
  forall (next : nat -> list LeakageEvent -> option FlatToRiscvDef.qLeakageEvent),
  exists finalTrace,
    forall (initial : MetricRiscvMachine) (P : MetricRiscvMachine -> Prop),
    valid_machine initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : MetricRiscvMachine =>
         P final /\
           (exists (tL : list LeakageEvent) (F : nat),
               getTrace final = (tL ++ getTrace initial)%list /\
                 (forall fuel : nat, (F <= fuel)%nat -> predictsLE (next fuel) (rev tL)))) ->
      FlatToRiscvCommon.runsTo initial
        (fun final : MetricRiscvMachine => P final /\ getTrace final = finalTrace ++ getTrace initial).
Proof.
  intros next.
  assert (H := a_trace_sorta_exists next).
  destruct H as [finalTrace H].
  assert (H' := last_step finalTrace).
  destruct H' as [n H'].
  exists (finalTrace n). intros initial P H1 H2.
  specialize (H initial P). specialize (H' initial P H1). apply H'. apply H. auto 20.
Qed.

    Lemma compiler_correct_wp': forall
        (* input of compilation: *)
        (fs: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (stack_lo stack_hi ret_addr p_funcs: word)
        (fname: string) next (f_rel_pos: Z),
        (*can i move these three hyps down below the exists?*)
        valid_src_funs fs = true ->
        compile fs = Success (instrs, finfo, req_stack_size) ->
        exists finalTrace, forall
        (* high-level initial state & post on final state: *)
        (k: trace) (t: io_trace) (mH: mem) (argvals: list word) (post: io_trace -> mem -> list word -> Prop) (initial: MetricRiscvMachine)
        (* ghost vars that help describe the low-level machine: *)
        (Rdata Rexec: mem -> Prop),
        NoDup (map fst fs) ->
        WeakestPrecondition.call fs fname k t mH argvals
          (fun k' t' m' rets =>
             post t' m' rets /\
               exists k'' F,
                 k' = k'' ++ k /\
                   forall fuel,
                     le F fuel ->
                     predicts (next tt fuel) (rev k'')) ->
        map.get (map.of_list finfo) fname = Some f_rel_pos ->
        req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
        word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
        initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
        map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
        word.unsigned ret_addr mod 4 = 0 ->
        arg_regs_contain initial.(getRegs) argvals ->
        initial.(getLog) = t ->
        machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
        FlatToRiscvCommon.runsTo initial (fun final : MetricRiscvMachine =>
          (exists mH' retvals,
            arg_regs_contain (getRegs final) retvals /\
            post final.(getLog) mH' retvals /\
            map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
            final.(getPc) = ret_addr /\
              machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final) /\
              final.(getTrace) = finalTrace ++ initial.(getTrace)).
    Proof.
      intros. Check compiler_correct_wp.
      assert (H' := compiler_correct_wp fs instrs finfo req_stack_size fname next f_rel_pos ltac:(assumption) ltac:(assumption)).
      destruct H' as [next' H']. Check predictor_thing_correct.
      assert (H'' := predictor_thing_correct (next' (p_funcs, f_rel_pos, stack_hi))).
      destruct H'' as [finalTrace H''].
      exists finalTrace. intros. apply H''.
      - destruct H11 as (H11_1 & H11_2 & H11_3 & H11_4 & H11_5 & H11_6 & H11_7). assumption.
      - eapply H'; eassumption.
    Qed.

    Lemma compiler_correct_wp'': forall
        (* input of compilation: *)
        (fs: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* part of function we choose to call: *)
        (stack_hi p_funcs: word)
        (fname: string) (f_rel_pos: Z),
        (*can i move these three hyps down below the exists?*)
        valid_src_funs fs = true ->
        compile fs = Success (instrs, finfo, req_stack_size) ->
        exists f, forall
          (* rest of function we choose to call: *)
          (stack_lo ret_addr : word)
          (* high-level initial state & post on final state: *)
          (k: trace) (t: io_trace) (mH: mem) (argvals: list word) (post: trace -> io_trace -> mem -> list word -> Prop) (initial: MetricRiscvMachine)
          (* ghost vars that help describe the low-level machine: *)
          (Rdata Rexec: mem -> Prop),
          NoDup (map fst fs) ->
          WeakestPrecondition.call fs fname k t mH argvals post ->
          map.get (map.of_list finfo) fname = Some f_rel_pos ->
          req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
          word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
          initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
          map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
          word.unsigned ret_addr mod 4 = 0 ->
          arg_regs_contain initial.(getRegs) argvals ->
          initial.(getLog) = t ->
          machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
          FlatToRiscvCommon.runsTo initial
            (fun final : MetricRiscvMachine =>
               (exists k'' mH' retvals,
                   arg_regs_contain (getRegs final) retvals /\
                     post (rev k'' ++ k) final.(getLog) mH' retvals /\
                     map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
                     final.(getPc) = ret_addr /\
                     machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final /\
                     (forall a,
                       generates a k'' ->
                       final.(getTrace) = f a ++ initial.(getTrace))
               )).
    Proof. Admitted.
    (* intros. Check predictor_works.
      assert (H' := compiler_correct_wp fs instrs finfo req_stack_size fname (fun _ _ => predictor a) f_rel_pos ltac:(assumption) ltac:(assumption)).
      destruct H' as [next' H']. Check predictor_thing_correct.
      assert (H'' := predictor_thing_correct (next' (p_funcs, f_rel_pos, stack_hi))).
      destruct H'' as [finalTrace H''].
      exists finalTrace. intros. apply H''.
      - destruct H11 as (H11_1 & H11_2 & H11_3 & H11_4 & H11_5 & H11_6 & H11_7). assumption.
      - eapply H'; try eassumption. eapply WeakestPreconditionProperties.Proper_call.
        2: eassumption. cbv [Morphisms.pointwise_relation Basics.impl].
        intros k_ t_ m_ argvals_ [H1' H2']. split; [assumption|]. destruct H1' as [k'' [H1' H3'] ].
        subst. exists k'', O. split; [reflexivity|]. intros. apply predictor_works.
        assumption.
    Qed.*)
  End WithMoreParams.
End WithWordAndMem.
