Require Import coqutil.Macros.unique.
Require Import coqutil.Decidable.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import coqutil.Z.Lia.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.Utility.
Require Import coqutil.Datatypes.ListSet.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.RegisterNames.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface.
Require Import compiler.SeparationLogic.
Require Import riscv.Spec.Decode.
Require Import compiler.Registers.
Require Import compiler.FlatImpConstraints.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Notation Register0 := 0%Z (only parsing).

Definition valid_instructions(iset: InstructionSet)(prog: list Instruction): Prop :=
  forall instr, In instr prog -> verify instr iset.

(* x0 is the constant 0, x1 is ra, x2 is sp, the others are usable *)
Definition valid_FlatImp_var(x: Z): Prop := 3 <= x < 32.

Lemma sp_not_valid_FlatImp_var: ~ valid_FlatImp_var RegisterNames.sp.
Proof. unfold valid_FlatImp_var, RegisterNames.sp. clear. blia. Qed.

Lemma ra_not_valid_FlatImp_var: ~ valid_FlatImp_var RegisterNames.ra.
Proof. unfold valid_FlatImp_var, RegisterNames.ra. clear. blia. Qed.

Lemma valid_FlatImp_var_implies_valid_register: forall (x: Z),
    valid_FlatImp_var x -> valid_register x.
Proof. unfold valid_FlatImp_var, valid_register. intros. blia. Qed.

Section FlatToRiscv1.

  (* Part 1: Definitions needed to state when compilation outputs valid code *)

  Definition valid_registers_bcond: bcond Z -> Prop := ForallVars_bcond valid_register.
  Definition valid_FlatImp_vars_bcond: bcond Z -> Prop := ForallVars_bcond valid_FlatImp_var.

  Lemma valid_FlatImp_vars_bcond_implies_valid_registers_bcond: forall b,
      valid_FlatImp_vars_bcond b -> valid_registers_bcond b.
  Proof.
    unfold valid_FlatImp_vars_bcond, valid_registers_bcond.
    intros. eauto using ForallVars_bcond_impl, valid_FlatImp_var_implies_valid_register.
  Qed.

  Definition valid_FlatImp_vars: stmt Z -> Prop := Forall_vars_stmt valid_FlatImp_var.

  Definition valid_FlatImp_fun: list Z * list Z * stmt Z -> Prop :=
    fun '(argnames, retnames, body) =>
      argnames = List.firstn (List.length argnames) (reg_class.all reg_class.arg) /\
      retnames = List.firstn (List.length retnames) (reg_class.all reg_class.arg) /\
      valid_FlatImp_vars body /\
      uses_standard_arg_regs body.


  Context (iset: InstructionSet).

  (* Part 2: compilation *)

  (* load & store depend on the bitwidth: on 32-bit machines, Lw just loads 4 bytes,
     while on 64-bit machines, it loads 4 bytes and sign-extends them.
     If we want a command which always loads 4 bytes without sign-extending them,
     we need to make a case distinction on the bitwidth and choose Lw on 32-bit,
     but Lwu on 64-bit.
     We can't just always choose Lwu, because Lwu is not available on 32-bit machines. *)

  Definition compile_load(sz: access_size):
    Z -> Z -> Z -> Instruction :=
    match sz with
    | access_size.one => Lbu
    | access_size.two => Lhu
    | access_size.four => if bitwidth iset =? 32 then Lw else Lwu
    | access_size.word => if bitwidth iset =? 32 then Lw else Ld
    end.

  Definition leak_Lbu x := ILeakage (Lbu_leakage x).
  Definition leak_Lhu x := ILeakage (Lhu_leakage x).
  Definition leak_Lw x := ILeakage (Lw_leakage x).
  Definition leak_Lwu x := I64Leakage (Lwu_leakage x).
  Definition leak_Ld x := I64Leakage (Ld_leakage x).

  Definition leak_load(sz: access_size) :
    Z -> LeakageEvent :=
    match sz with
    | access_size.one => leak_Lbu
    | access_size.two => leak_Lhu
    | access_size.four => if bitwidth iset =? 32 then leak_Lw else leak_Lwu
    | access_size.word => if bitwidth iset =? 32 then leak_Lw else leak_Ld
    end.

  Definition compile_store(sz: access_size):
    Z -> Z -> Z -> Instruction :=
    match sz with
    | access_size.one => Sb
    | access_size.two => Sh
    | access_size.four => Sw
    | access_size.word => if bitwidth iset =? 32 then Sw else Sd
    end.

  Definition leak_Sb x := ILeakage (Sb_leakage x).
  Definition leak_Sh x := ILeakage (Sh_leakage x).
  Definition leak_Sw x := ILeakage (Sw_leakage x).
  Definition leak_Sd x := I64Leakage (Sd_leakage x).

  Definition leak_store(sz: access_size) :
    Z -> LeakageEvent :=
    match sz with
    | access_size.one => leak_Sb
    | access_size.two => leak_Sh
    | access_size.four => leak_Sw
    | access_size.word => if bitwidth iset =? 32 then leak_Sw else leak_Sd
    end.

  Definition compile_op_imm(rd: Z)(op: Syntax.bopname)(rs1: Z)(c2: Z): list Instruction :=
    match op with
    | Syntax.bopname.add => [[Addi rd rs1 c2]]
    | Syntax.bopname.and => [[Andi rd rs1 c2]]
    | Syntax.bopname.or  => [[Ori  rd rs1 c2]]
    | Syntax.bopname.xor => [[Xori rd rs1 c2]]
    | Syntax.bopname.sru => [[Srli rd rs1 c2]]
    | Syntax.bopname.slu => [[Slli rd rs1 c2]]
    | Syntax.bopname.srs => [[Srai rd rs1 c2]]
    | Syntax.bopname.lts => [[Slti rd rs1 c2]]
    | Syntax.bopname.ltu => [[Sltiu rd rs1 c2]]
    | _ => [InvalidInstruction (-1)]
    end.

  Definition leak_Addi := ILeakage Addi_leakage.
  Definition leak_Andi := ILeakage Andi_leakage.
  Definition leak_Ori := ILeakage Ori_leakage.
  Definition leak_Xori := ILeakage Xori_leakage.
  Definition leak_Srli := ILeakage Srli_leakage.
  Definition leak_Slli := ILeakage Slli_leakage.
  Definition leak_Srai := ILeakage Srai_leakage.
  Definition leak_Slti := ILeakage Slti_leakage.
  Definition leak_Sltiu := ILeakage Sltiu_leakage.

  Definition leak_op_imm(op: Syntax.bopname) : option LeakageEvent :=
    match op with
    | Syntax.bopname.add => Some leak_Addi
    | Syntax.bopname.and => Some leak_Andi
    | Syntax.bopname.or  => Some leak_Ori
    | Syntax.bopname.xor => Some leak_Xori
    | Syntax.bopname.sru => Some leak_Srli
    | Syntax.bopname.slu => Some leak_Slli
    | Syntax.bopname.srs => Some leak_Srai
    | Syntax.bopname.lts => Some leak_Slti
    | Syntax.bopname.ltu => Some leak_Sltiu
    | _ => None (* ?? why are there invalid instructions again - doesn't compilation just fail? *)
    end.

  Definition compile_op_register(rd: Z)(op: Syntax.bopname)(rs1 rs2: Z): list Instruction :=
    match op with
    | Syntax.bopname.add => [[Add rd rs1 rs2]]
    | Syntax.bopname.sub => [[Sub rd rs1 rs2]]
    | Syntax.bopname.mul => [[Mul rd rs1 rs2]]
    | Syntax.bopname.mulhuu => [[Mulhu rd rs1 rs2]]
    | Syntax.bopname.divu => [[Divu rd rs1 rs2]]
    | Syntax.bopname.remu => [[Remu rd rs1 rs2]]
    | Syntax.bopname.and => [[And rd rs1 rs2]]
    | Syntax.bopname.or  => [[Or  rd rs1 rs2]]
    | Syntax.bopname.xor => [[Xor rd rs1 rs2]]
    | Syntax.bopname.sru => [[Srl rd rs1 rs2]]
    | Syntax.bopname.slu => [[Sll rd rs1 rs2]]
    | Syntax.bopname.srs => [[Sra rd rs1 rs2]]
    | Syntax.bopname.lts => [[Slt rd rs1 rs2]]
    | Syntax.bopname.ltu => [[Sltu rd rs1 rs2]]
    | Syntax.bopname.eq  => [[Sub rd rs1 rs2; Seqz rd rd]]
    end.

  Definition leak_Add := ILeakage Add_leakage.
  Definition leak_Sub := ILeakage Sub_leakage.
  Definition leak_Mul := MLeakage Mul_leakage.
  Definition leak_Mulhu := MLeakage Mulhu_leakage.
  Definition leak_Divu := MLeakage Divu_leakage.
  Definition leak_Remu := MLeakage Remu_leakage.
  Definition leak_And := ILeakage And_leakage.
  Definition leak_Or := ILeakage Or_leakage.
  Definition leak_Xor := ILeakage Xor_leakage.
  Definition leak_Srl := ILeakage Srl_leakage.
  Definition leak_Sll := ILeakage Sll_leakage.
  Definition leak_Sra := ILeakage Sra_leakage.
  Definition leak_Slt := ILeakage Slt_leakage.
  Definition leak_Sltu := ILeakage Sltu_leakage.
  Print Seqz. (* Seqz = fun rd rs : Z => Sltiu rd rs 1 : Z -> Z -> InstructionI *)
  Definition leak_Seqz := ILeakage Sltiu_leakage.
  
  Definition leak_op_register (op: Syntax.bopname) : list LeakageEvent :=
    match op with
    | Syntax.bopname.add => [ leak_Add ]
    | Syntax.bopname.sub => [ leak_Sub ]
    | Syntax.bopname.mul => [ leak_Mul ]
    | Syntax.bopname.mulhuu => [ leak_Mulhu ]
    | Syntax.bopname.divu => [ leak_Divu ] 
    | Syntax.bopname.remu => [ leak_Remu ]
    | Syntax.bopname.and => [ leak_And ]
    | Syntax.bopname.or  => [ leak_Or ]
    | Syntax.bopname.xor => [ leak_Xor ]
    | Syntax.bopname.sru => [ leak_Srl ]
    | Syntax.bopname.slu => [ leak_Sll ]
    | Syntax.bopname.srs => [ leak_Sra ]
    | Syntax.bopname.lts => [ leak_Slt ]
    | Syntax.bopname.ltu => [ leak_Sltu ]
    | Syntax.bopname.eq  => [ leak_Sub ; leak_Seqz ]
    end.
  
  Definition compile_op(rd: Z)(op: Syntax.bopname)(op1 : Z)(op2: operand): list Instruction :=
    match  op2 with
    | Var v2 => compile_op_register rd op op1 v2
    | Const c2 => compile_op_imm rd op op1 c2
    end.

  Definition leak_op (op : Syntax.bopname) (op2: @operand Z) : option (list LeakageEvent) :=
    match op2 with
    | Var _ => Some (leak_op_register op)
    | Const _ => option_map (fun x => [x]) (leak_op_imm op)
    end.

  Definition compile_lit_12bit(rd: Z)(v: Z): list Instruction :=
    [[ Addi rd Register0 (signExtend 12 v) ]].

  Definition leak_lit_12bit : list LeakageEvent :=
    [ leak_Addi ].

  (* On a 64bit machine, loading a constant -2^31 <= v < 2^31 is not always possible with
     a Lui followed by an Addi:
     If the constant is of the form 0x7ffffXXX, and XXX has its highest bit set, we would
     have to put 0x80000--- into the Lui, but then that value will be sign-extended.

     Or spelled differently:
     If we consider all possible combinations of a Lui followed by an Addi, we get 2^32
     different values, but some of them are not in the range -2^31 <= v < 2^31.
     On the other hand, this property holds for combining Lui followed by a Xori.

     Or yet differently:
     Lui 0x80000--- ; Addi 0xXXX
     where XXX has the highest bit set,
     loads a value < 2^31, so some Lui+Addi pairs do not load a value in the range
     -2^31 <= v < 2^31, so some Lui+Addi pairs are "wasted" and we won't find a
     Lui+Addi pairs for all desired values in the range -2^31 <= v < 2^31
 *)

  Definition compile_lit_32bit(rd: Z)(v: Z): list Instruction :=
    let lo := signExtend 12 v in
    let hi := Z.lxor (signExtend 32 v) lo in
    [[ Lui rd hi ; Xori rd rd lo ]].

  Definition leak_Lui := ILeakage Lui_leakage.

  Definition leak_lit_32bit : list LeakageEvent :=
    [ leak_Xori ; leak_Lui ].

  Definition compile_lit_64bit(rd: Z)(v: Z): list Instruction :=
    let v0 := bitSlice v  0 11 in
    let v1 := bitSlice v 11 22 in
    let v2 := bitSlice v 22 32 in
    let hi := bitSlice v 32 64 in
    compile_lit_32bit rd (signExtend 32 hi) ++
    [[ Slli rd rd 10 ;
       Xori rd rd v2 ;
       Slli rd rd 11 ;
       Xori rd rd v1 ;
       Slli rd rd 11 ;
       Xori rd rd v0 ]].

  Definition leak_lit_64bit : list LeakageEvent :=
    [ leak_Xori ;
      leak_Slli ;
      leak_Xori ;
      leak_Slli ;
      leak_Xori ;
      leak_Slli ] ++
      leak_lit_32bit.

  Definition compile_lit(rd: Z)(v: Z): list Instruction :=
    if ((-2^11 <=? v)%Z && (v <? 2^11)%Z)%bool then
      compile_lit_12bit rd v
    else if ((bitwidth iset =? 32)%Z || (- 2 ^ 31 <=? v)%Z && (v <? 2 ^ 31)%Z)%bool then
      compile_lit_32bit rd v
    else compile_lit_64bit rd v.

  Definition leak_lit(v: Z) : list LeakageEvent :=
    if ((-2^11 <=? v)%Z && (v <? 2^11)%Z)%bool then
      leak_lit_12bit
    else if ((bitwidth iset =? 32)%Z || (- 2 ^ 31 <=? v)%Z && (v <? 2 ^ 31)%Z)%bool then
      leak_lit_32bit
    else leak_lit_64bit.

  (* Inverts the branch condition. *)
  Definition compile_bcond_by_inverting
             (cond: bcond Z) (amt: Z) : Instruction:=
    match cond with
    | CondBinary op x y =>
        match op with
        | BEq  => Bne x y amt
        | BNe  => Beq x y amt
        | BLt  => Bge x y amt
        | BGe  => Blt x y amt
        | BLtu => Bgeu x y amt
        | BGeu => Bltu x y amt
        end
    | CondNez x =>
        Beq x Register0 amt
    end.

  Definition leak_Bne x := ILeakage (Bne_leakage x).
  Definition leak_Beq x := ILeakage (Beq_leakage x).
  Definition leak_Bge x := ILeakage (Bge_leakage x).
  Definition leak_Blt x := ILeakage (Blt_leakage x).
  Definition leak_Bgeu x := ILeakage (Bgeu_leakage x).
  Definition leak_Bltu x := ILeakage (Bltu_leakage x).

  Definition leak_bcond_by_inverting
    (cond: bcond Z) : bool -> LeakageEvent :=
    match cond with
    | CondBinary op _ _ =>
        match op with
        | BEq  => leak_Bne
        | BNe  => leak_Beq
        | BLt  => leak_Bge
        | BGe  => leak_Blt
        | BLtu => leak_Bgeu
        | BGeu => leak_Bltu
        end
    | CondNez _ =>
        leak_Beq
    end.

  Local Notation bytes_per_word := (Memory.bytes_per_word (bitwidth iset)).

  Fixpoint save_regs(regs: list Z)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_store access_size.word sp r offset
                   :: (save_regs regs (offset + bytes_per_word))
    end. Print leak_store. Print compile_store.

  Fixpoint leak_save_regs(sp_val: Z)(regs: list Z)(offset: Z): list LeakageEvent :=
    match regs with
    | nil => nil
    | r :: regs' => leak_save_regs sp_val regs' (offset + bytes_per_word) ++
                      [leak_store access_size.word (sp_val + offset)]
    end.

  Fixpoint load_regs(regs: list Z)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_load access_size.word r sp offset
                   :: (load_regs regs (offset + bytes_per_word))
    end.

  Fixpoint leak_load_regs(sp_val: Z)(regs: list Z)(offset: Z): list LeakageEvent :=
    match regs with
    | nil => nil
    | r :: regs' => leak_load_regs sp_val regs' (offset + bytes_per_word) ++
                      [leak_load access_size.word (sp_val + offset)]
    end.

  (* number of words of stack allocation space needed within current frame *)
  Fixpoint stackalloc_words(s: stmt Z): Z :=
    match s with
    | SLoad _ _ _ _ | SStore _ _ _ _ | SInlinetable _ _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _
    | SSkip | SCall _ _ _ | SInteract _ _ _ => 0
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => Z.max (stackalloc_words s1) (stackalloc_words s2)
    (* ignore negative values, and round up values that are not divisible by bytes_per_word *)
    | SStackalloc x n body => (Z.max 0 n + bytes_per_word - 1) / bytes_per_word
                              + stackalloc_words body
    end.

  Definition compile4bytes(l: list byte): Instruction :=
    InvalidInstruction (LittleEndian.combine 4 (HList.tuple.of_list [
      nth 0 l Byte.x00;
      nth 1 l Byte.x00;
      nth 2 l Byte.x00;
      nth 3 l Byte.x00
    ])).

  Fixpoint compile_byte_list(l: list byte): list Instruction :=
    match l with
    | b0 :: b1 :: b2 :: b3 :: rest => compile4bytes l :: compile_byte_list rest
    | nil => nil
    | _ => [compile4bytes l]
    end.

  (* All positions are relative to the beginning of the progam, so we get completely
     position independent code. *)

  Context {env: map.map String.string (list Z * list Z * stmt Z)}.
  Check Semantics.abstract_trace.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.
  Context {pos_map: map.map String.string Z}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).
  Context (leak_ext_call: env -> Z (*sp_val*) -> Z (*stackoffset*) -> stmt Z -> list LeakageEvent).

  Section WithOtherEnv.
    Variable e: env. Print LeakageEvent.

    Definition leak_Jal := ILeakage Jal_leakage.
    Definition leak_Jalr := ILeakage Jalr_leakage. Check @map.get.

    Fixpoint transform_trace
      (* maps a source-level abstract trace to a target-level trace.
         executes s, guided by t, popping events off of t and adding events to l as it goes.
         returns the final leakage l, along with the part of t that remains after we finish
                 executing s.
         may (but will not necessarily) return None if input is garbage.
         *)
      (magicFuel : nat) (s : stmt Z) (sp_val : Z) (stackoffset : Z) (t : Semantics.abstract_trace) :
      option (Semantics.abstract_trace * list LeakageEvent) :=
      
      match magicFuel with
      | O => None
      | S magicFuel' => let transform_trace := transform_trace magicFuel' in
                        match s with
                        | SLoad _ _ _ _ =>
                            match t with
                            | Semantics.cons_read sz a t' => Some (t', [ leak_load sz (word.unsigned a) ])
                            | _ => None
                            end
                        | SStore _ _ _ _ =>
                            match t with
                            | Semantics.cons_write sz a t' => Some (t', [ leak_store sz (word.unsigned a) ])
                            | _ => None
                            end
                        | SInlinetable sz x t i =>
                            None (* TODO: what is this?  why are there invalid instructions? *)
                        | SStackalloc _ n body =>
                            match t with
                            | Semantics.cons_salloc f =>
                                let t' := f (word.of_Z (sp_val + stackoffset - n)) in
                                match transform_trace body sp_val (stackoffset - n) t' with
                                | Some (t'', l) => Some (t'', l ++ [ leak_Addi ])
                                | None => None
                                end
                            | _ => None
                            end
                        | SLit _ v => Some (t, leak_lit v)
                        | SOp _ op _ operand2 =>
                            match leak_op op operand2 with
                            | Some l' => Some (t, l')
                            | None => None
                            end
                        | SSet _ _ => Some (t, [ leak_Add ])
                        | SIf cond bThen bElse =>
                            match t with
                            | Semantics.cons_branch b t' =>
                                let lCond := [ leak_bcond_by_inverting cond (negb b) ] in
                                match b with
                                | true =>
                                    match transform_trace bThen sp_val stackoffset t' with
                                    | Some (t'', lThen) => Some (t'', lCond ++ lThen ++ [ leak_Jal ])
                                    | None => None
                                    end
                                | false =>
                                    match transform_trace bElse sp_val stackoffset t' with
                                    | Some (t'', lElse) => Some (t'', lCond ++ lElse)
                                    | None => None
                                    end
                                end
                            | _ => None
                            end
                        | SLoop body1 cond body2 =>
                            match transform_trace body1 sp_val stackoffset t with
                            | Some (t', lBody1) =>
                                match t' with
                                | Semantics.cons_branch b t'' =>
                                    let lCond := [ leak_bcond_by_inverting cond (negb b) ] in
                                    match b with
                                    | true =>
                                        match transform_trace body2 sp_val stackoffset t'' with
                                        | Some (t''', lBody2) =>
                                            match transform_trace s sp_val stackoffset t''' with
                                            | Some (t'''', lLoop) => Some (t''', lBody1 ++ lCond ++ lBody2 ++ [ leak_Jal ])
                                            | None => None
                                            end
                                        | None => None
                                        end
                                    | false => Some (t'', lBody1 ++ lCond)
                                    end
                                | _ => None
                                end
                            | None => None
                            end
                        | SSeq s1 s2 =>
                            match transform_trace s1 sp_val stackoffset t with
                            | Some (t', l1) =>
                                match transform_trace s2 sp_val stackoffset t' with
                                | Some (t'', l2) => Some (t'', l1 ++ l2)
                                | None => None
                                end
                            | None => None
                            end
                        | SSkip => Some (t, nil)
                        | SCall resvars fname argvars =>
                            match @map.get _ _ env e fname with
                            | Some (params, rets, fbody) =>
                                let need_to_save := list_diff Z.eqb (modVars_as_list Z.eqb fbody) resvars in
                                let scratchwords := stackalloc_words fbody in
                                let framesize := bytes_per_word *
                                                   (Z.of_nat (1 + length need_to_save) + scratchwords) in
                                let sp_val' := sp - framesize in
                                let l' :=
                                  [ leak_Jal ] ++ (* jump to compiled function *)
                                    [ leak_Addi ] ++ (* Addi sp sp (-framesize) *)
                                    [ leak_store access_size.word
                                        (sp_val' + bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)) ] ++
                                    leak_save_regs sp_val' need_to_save (bytes_per_word * scratchwords) in
                                match transform_trace fbody sp_val' (bytes_per_word * scratchwords) t
                                (*    ^nonterminating :( *) with
                                | Some (t'', lBody) =>
                                    let l'' :=
                                      l' ++
                                        leak_load_regs sp_val' need_to_save (bytes_per_word * scratchwords) ++
                                        [ leak_load access_size.word
                                            (sp_val' + bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)) ] ++
                                        [ leak_Addi ] ++ (* Addi sp sp framesize *)
                                        [ leak_Jalr ] in
                                    Some (t'', l'')
                                | None => None
                                end
                            | None => None
                            end
                        | SInteract _ _ _ => Some (t, leak_ext_call e sp_val stackoffset s)
                        end
      end.
  End WithOtherEnv.

  Section WithEnv.
    Variable e: pos_map.

    (* mypos: position of the code relative to the positions in e
       stackoffset: $sp + stackoffset is the (last) highest used stack address (for SStackalloc)
       s: statement to be compiled *)
    Fixpoint compile_stmt(mypos: Z)(stackoffset: Z)(s: stmt Z): list Instruction :=
      match s with
      | SLoad  sz x y ofs => [[compile_load  sz x y ofs]]
      | SStore sz x y ofs => [[compile_store sz x y ofs]]
      | SInlinetable sz x t i =>
        let bs := compile_byte_list t in
        [[ Jal x (4 + Z.of_nat (length bs) * 4) ]] ++ bs ++ [[ Add x x i; compile_load sz x x 0 ]]
      | SStackalloc x n body =>
          [[Addi x sp (stackoffset-n)]] ++ compile_stmt (mypos + 4) (stackoffset-n) body
      | SLit x v => compile_lit x v
      | SOp x op y z => compile_op x op y z
      | SSet x y => [[Add x Register0 y]]
      | SIf cond bThen bElse =>
          let bThen' := compile_stmt (mypos + 4) stackoffset bThen in
          let bElse' := compile_stmt (mypos + 4 + 4 * Z.of_nat (length bThen') + 4) stackoffset bElse in
          (* only works if branch lengths are < 2^12 *)
          [[compile_bcond_by_inverting cond ((Z.of_nat (length bThen') + 2) * 4)]] ++
          bThen' ++
          [[Jal Register0 ((Z.of_nat (length bElse') + 1) * 4)]] ++
          bElse'
      | SLoop body1 cond body2 =>
          let body1' := compile_stmt mypos stackoffset body1 in
          let body2' := compile_stmt (mypos + (Z.of_nat (length body1') + 1) * 4) stackoffset body2 in
          (* only works if branch lengths are < 2^12 *)
          body1' ++
          [[compile_bcond_by_inverting cond ((Z.of_nat (length body2') + 2) * 4)]] ++
          body2' ++
          [[Jal Register0 (- Z.of_nat (length body1' + 1 + length body2') * 4)]]
      | SSeq s1 s2 =>
          let s1' := compile_stmt mypos stackoffset s1 in
          let s2' := compile_stmt (mypos + 4 * Z.of_nat (length s1')) stackoffset s2 in
          s1' ++ s2'
      | SSkip => nil
      | SCall resvars f argvars =>
        let fpos := match map.get e f with
                    | Some pos => pos
                    (* don't fail so that we can measure the size of the resulting code *)
                    | None => 42
                    end in
        [[ Jal ra (fpos - mypos) ]]
      | SInteract _ _ _ => compile_ext_call e mypos stackoffset s
      end.

    (*
     Stack layout:

     high addresses              ...
                      old sp --> begin of stack scratch space of previous function
                                 ra
                                 mod_var_n
                                 ...
                                 mod_var_0
                                 end of stack scratch space of current function
                                 ...  (stack scratch space also grows downwards, from "end" to "begin")
                      new sp --> begin of stack scratch space of current function
     low addresses               ...

     Expected stack layout at beginning of function call: like above, but only filled up to arg0.
     Stack grows towards low addresses.
    *)
    Definition compile_function(mypos: Z):
      (list Z * list Z * stmt Z) -> list Instruction :=
      fun '(argvars, resvars, body) =>
        let need_to_save := list_diff Z.eqb (modVars_as_list Z.eqb body) resvars in
        let scratchwords := stackalloc_words body in
        let framesize := bytes_per_word *
                         (Z.of_nat (1 + length need_to_save) + scratchwords) in
        [[ Addi sp sp (-framesize) ]] ++
        [[ compile_store access_size.word sp ra
                         (bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)) ]] ++
        save_regs need_to_save (bytes_per_word * scratchwords) ++
        compile_stmt (mypos + 4 * (2 + Z.of_nat (length need_to_save)))
                     (bytes_per_word * scratchwords) body ++
        load_regs need_to_save (bytes_per_word * scratchwords) ++
        [[ compile_load access_size.word ra sp
                        (bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)) ]] ++
        [[ Addi sp sp framesize ]] ++
        [[ Jalr zero ra 0 ]].

    Definition add_compiled_function(state: list Instruction * pos_map)(fname: String.string)
               (fimpl: list Z * list Z * stmt Z): list Instruction * pos_map :=
      let '(old_insts, infomap) := state in
      let pos := 4 * Z.of_nat (length (old_insts)) in
      let new_insts := compile_function pos fimpl in
      let '(argnames, retnames, fbody) := fimpl in
      (old_insts ++ new_insts,
       map.put infomap fname pos).

    Definition compile_funs: env -> list Instruction * pos_map :=
      map.fold add_compiled_function (nil, map.empty).
  End WithEnv.

  (* compiles all functions just to obtain their code size *)
  Definition build_fun_pos_env(e_impl: env): pos_map :=
    (* since we pass map.empty as the fun_pos_env into compile_funs, the instrs
       returned don't jump to the right positions yet (they all jump to 42),
       but the instructions have the right size, so the posmap we return is correct *)
    snd (compile_funs map.empty e_impl).

End FlatToRiscv1.
