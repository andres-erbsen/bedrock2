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
  Context {width} {BW: Bitwidth width} {word: word.word width}.
 
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
    word -> LeakageEvent :=
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
    word -> LeakageEvent :=
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
  Definition leak_Srli (imm : Z) := ILeakage (Srli_leakage imm).
  Definition leak_Slli (imm : Z) := ILeakage (Slli_leakage imm).
  Definition leak_Srai (imm : Z) := ILeakage (Srai_leakage imm).
  Definition leak_Slti := ILeakage Slti_leakage.
  Definition leak_Sltiu := ILeakage Sltiu_leakage.

  Definition leak_op_imm(op: Syntax.bopname) (c2 : Z) : option LeakageEvent :=
    match op with
    | Syntax.bopname.add => Some leak_Addi
    | Syntax.bopname.and => Some leak_Andi
    | Syntax.bopname.or  => Some leak_Ori
    | Syntax.bopname.xor => Some leak_Xori
    | Syntax.bopname.sru => Some (leak_Srli c2)
    | Syntax.bopname.slu => Some (leak_Slli c2)
    | Syntax.bopname.srs => Some (leak_Srai c2)
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
  Definition leak_Divu (num den : word) := MLeakage (Divu_leakage num den).
  Definition leak_Remu (num den : word) := MLeakage (Remu_leakage num den).
  Definition leak_And := ILeakage And_leakage.
  Definition leak_Or := ILeakage Or_leakage.
  Definition leak_Xor := ILeakage Xor_leakage.
  Definition leak_Srl (shamt : word) := ILeakage (Srl_leakage shamt).
  Definition leak_Sll (shamt : word) := ILeakage (Sll_leakage shamt).
  Definition leak_Sra (shamt : word) := ILeakage (Sra_leakage shamt).
  Definition leak_Slt := ILeakage Slt_leakage.
  Definition leak_Sltu := ILeakage Sltu_leakage.
  Definition leak_Seqz := ILeakage Sltiu_leakage.
  
  Definition leak_op_register (op: Syntax.bopname) (x1 x2 : word) : list LeakageEvent :=
    match op with
    | Syntax.bopname.add => [ leak_Add ]
    | Syntax.bopname.sub => [ leak_Sub ]
    | Syntax.bopname.mul => [ leak_Mul ]
    | Syntax.bopname.mulhuu => [ leak_Mulhu ]
    | Syntax.bopname.divu => [ leak_Divu x1 x2 ] 
    | Syntax.bopname.remu => [ leak_Remu x1 x2 ]
    | Syntax.bopname.and => [ leak_And ]
    | Syntax.bopname.or  => [ leak_Or ]
    | Syntax.bopname.xor => [ leak_Xor ]
    | Syntax.bopname.sru => [ leak_Srl x2 ]
    | Syntax.bopname.slu => [ leak_Sll x2 ]
    | Syntax.bopname.srs => [ leak_Sra x2 ]
    | Syntax.bopname.lts => [ leak_Slt ]
    | Syntax.bopname.ltu => [ leak_Sltu ]
    | Syntax.bopname.eq  => [ leak_Sub ; leak_Seqz ]
    end.
  
  Definition compile_op(rd: Z)(op: Syntax.bopname)(op1 : Z)(op2: operand): list Instruction :=
    match  op2 with
    | Var v2 => compile_op_register rd op op1 v2
    | Const c2 => compile_op_imm rd op op1 c2
    end. Check Const.

  Definition leak_op (op : Syntax.bopname) (op2: @operand Z) (x1 x2 : word) :
    option (list LeakageEvent) :=
    match op2 with
    | Var _ => Some (leak_op_register op x1 x2)
    | Const c2 => option_map (fun x => [x]) (leak_op_imm op c2)
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
    [ leak_Lui ; leak_Xori ].

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
    leak_lit_32bit ++
    [ leak_Slli 10 ;
      leak_Xori ;
      leak_Slli 11 ;
      leak_Xori ;
      leak_Slli 11 ;
      leak_Xori ].

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
    end.

  Fixpoint leak_save_regs
    (sp_val: word)(regs: list Z)(offset: Z): list LeakageEvent :=
    match regs with
    | nil => nil
    | r :: regs' => [leak_store access_size.word (word.add sp_val (word.of_Z offset))] ++
                      leak_save_regs sp_val regs' (offset + bytes_per_word)
    end.
  
  Fixpoint load_regs(regs: list Z)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_load access_size.word r sp offset
                   :: (load_regs regs (offset + bytes_per_word))
    end.

  Fixpoint leak_load_regs
    (sp_val: word)(regs: list Z)(offset: Z): list LeakageEvent :=
    match regs with
    | nil => nil
    | r :: regs' => [leak_load access_size.word (word.add sp_val (word.of_Z offset))] ++
                      leak_load_regs sp_val regs' (offset + bytes_per_word)
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

  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * stmt Z)}.
  Context {pos_map: map.map String.string Z}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).
  Context (leak_ext_call: (*env -> Z (*sp_val*) -> Z (*stackoffset*) -> stmt Z ->*) list LeakageEvent).

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

    Section WithOtherEnv.
    Context (program_base : word).
    Variable e_env: env.

    Definition leak_Jal := ILeakage Jal_leakage.
    Definition leak_Jalr := ILeakage Jalr_leakage.

    Inductive qLeakageEvent :=
    | qLE (le : LeakageEvent)
    | qendLE.

    Definition quotLE (e : LeakageEvent) : qLeakageEvent := qLE e.
    
    Print Semantics.predict_with_prefix.
    Notation trace := Semantics.trace.

    Notation event := Semantics.event.
  
    Notation qevent := Semantics.qevent. Search qevent.
    Notation quot := Semantics.quot. Print Semantics.qevent.
    Notation qleak_bool := Semantics.qleak_bool.
    Notation qleak_word := Semantics.qleak_word.
    Notation qconsume := Semantics.qconsume.
    Notation qend := Semantics.qend.

    Notation leak_bool := Semantics.leak_bool.
    Notation leak_word := Semantics.leak_word.
    Notation consume_bool := Semantics.consume_bool.
    Notation consume_word := Semantics.consume_word.

    Fixpoint predictLE_with_prefix (prefix : list LeakageEvent) (predict_rest : list LeakageEvent -> option qLeakageEvent) (t : list LeakageEvent) : option qLeakageEvent :=
    match prefix, t with
    | _ :: prefix', _ :: t' => predictLE_with_prefix prefix' predict_rest t'
    | e :: start', nil => Some (quotLE e)
    | nil, _ => predict_rest t
    end.

    Definition rnext_fun' rnext_stmt (fuel : nat) (next : trace -> option qevent) (t_so_far : trace)
      (mypos : Z)
      (sp_val : word) (params rets : list Z) fbody (rt_so_far : list LeakageEvent)
      (f : forall (t_so_far : trace) (rt_so_far : list LeakageEvent), option qLeakageEvent)
      : option qLeakageEvent :=
      let need_to_save := list_diff Z.eqb (modVars_as_list Z.eqb fbody) rets in
                  let scratchwords := stackalloc_words fbody in
                  let framesize := bytes_per_word *
                                     (Z.of_nat (length need_to_save) + 1 + scratchwords) in
                  let sp_val' := word.add sp_val (word.of_Z (-framesize)) in
                  let beforeBody :=
                      [ leak_Addi ] ++ (* Addi sp sp (-framesize) *)
                      [ leak_store access_size.word
                          (word.add sp_val' (word.of_Z (bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)))) ] ++
                      leak_save_regs sp_val' need_to_save (bytes_per_word * scratchwords) in
                  let afterBody :=
                    leak_load_regs sp_val' need_to_save (bytes_per_word * scratchwords) ++
                      [ leak_load access_size.word
                          (word.add sp_val' (word.of_Z (bytes_per_word * (Z.of_nat (length need_to_save) + scratchwords)))) ] ++
                      [ leak_Addi ] ++ (* Addi sp sp framesize *)
                      [ leak_Jalr ] in
                  
                  predictLE_with_prefix
                    beforeBody
                    (fun rt_so_far' =>
                       rnext_stmt fuel next t_so_far
                         (mypos + 4 * (2 + Z.of_nat (length need_to_save))) sp_val'
                         (bytes_per_word * scratchwords) fbody rt_so_far'
                         (fun t_so_far' rt_so_far'' =>
                            predictLE_with_prefix
                              afterBody
                              (f t_so_far')
                              rt_so_far''))
                    rt_so_far.

    Check (match 5%nat with | S _ | O => 5%nat end).

    Fixpoint rnext_stmt (fuel : nat) (next : trace -> option qevent) (t_so_far : trace)
      (myPos : Z)
      (sp_val : word) (stackoffset : Z) (s : stmt Z) (rt_so_far : list LeakageEvent)
      (f : forall (t_so_far : trace) (rt_so_far : list LeakageEvent), option qLeakageEvent)
      : option qLeakageEvent :=
      match fuel with
      | O => None
      | S fuel' =>
          let rnext_stmt0 := rnext_stmt in
          let rnext_stmt := rnext_stmt fuel' next in
          match s with
          | SLoad sz x y o =>
              match next t_so_far with
              | Some (qleak_word a) =>
                  predictLE_with_prefix
                    [leak_load sz a]
                    (f (t_so_far ++ [leak_word a]))
                    rt_so_far
              | _ => None
              end
          | SStore sz x y o =>
              match next t_so_far with
              | Some (qleak_word a) =>
                  predictLE_with_prefix
                    [leak_store sz a]
                    (f (t_so_far ++ [leak_word a]))
                    rt_so_far
              | _ => None
              end
          | SInlinetable sz x t i =>
              match next t_so_far with
              | Some (qleak_word i') =>
                  predictLE_with_prefix
                    [leak_Jal; leak_Add; leak_load sz (word.add (word.add (word.add program_base (word.of_Z myPos)) (word.of_Z 4)) i')]
                    (f (t_so_far ++ [leak_word i']))
                    rt_so_far
              | _ => None
              end
          | SStackalloc _ n body =>
              let a := (word.add sp_val (word.of_Z (stackoffset - n))) in
              predictLE_with_prefix
                [ leak_Addi ]
                (fun rt_so_far' => rnext_stmt (t_so_far ++ [consume_word a]) (myPos + 4) sp_val (stackoffset - n) body rt_so_far' f)
                rt_so_far
          | SLit _ v =>
              predictLE_with_prefix
                (leak_lit v)
                (f t_so_far)
                rt_so_far
          | SOp _ op _ operand2 =>
              let newt_operands :=
                match op with
                | Syntax.bopname.divu
                | Syntax.bopname.remu =>
                    match next t_so_far with
                    | Some (qleak_word x1) =>
                        match next (t_so_far ++ [leak_word x1]) with
                        | Some (qleak_word x2) => Some ([leak_word x1; leak_word x2], x1, x2)
                        | _ => None
                        end
                    | _ => None
                    end
                | Syntax.bopname.slu
                | Syntax.bopname.sru
                | Syntax.bopname.srs =>
                    match next t_so_far with
                    | Some (qleak_word x2) => Some ([leak_word x2], word.of_Z 0, x2)
                    | _ => None
                    end
                | _ => Some ([], word.of_Z 0, word.of_Z 0)
                end
              in
              match newt_operands with
              | Some (newt, x1, x2) =>
                  match leak_op op operand2 x1 x2 with
                  | Some l =>
                      predictLE_with_prefix
                        l
                        (f (t_so_far ++ newt))
                        rt_so_far
                  | None => None
                  end
              | None => None
              end
          | SSet _ _ =>
              predictLE_with_prefix
                [ leak_Add ]
                (f t_so_far)
                rt_so_far
          | SIf cond bThen bElse =>
              let thenLength := Z.of_nat (length (compile_stmt (myPos + 4) stackoffset bThen)) in
              match next t_so_far with
              | Some (qleak_bool b) =>
                  predictLE_with_prefix
                    [ leak_bcond_by_inverting cond (negb b) ]
                    (fun rt_so_far' => rnext_stmt (t_so_far ++ [leak_bool b])
                                         (if b then (myPos + 4) else (myPos + 4 + 4 * thenLength + 4))
                                         sp_val stackoffset (if b then bThen else bElse) rt_so_far'
                                         (fun t_so_far' rt_so_far'' =>
                                            predictLE_with_prefix
                                              (if b then [leak_Jal] else [])
                                              (f t_so_far')
                                              rt_so_far''))
                    rt_so_far
              | _ => None
              end
          | SLoop body1 cond body2 =>
              let body1Length := Z.of_nat (length (compile_stmt myPos stackoffset body1)) in
              rnext_stmt t_so_far myPos sp_val stackoffset body1 rt_so_far
                (fun t_so_far' rt_so_far' =>
                   match next t_so_far' with
                   | Some (qleak_bool true) =>
                       predictLE_with_prefix
                         [ leak_bcond_by_inverting cond (negb true) ]
                         (fun rt_so_far'' =>
                            rnext_stmt (t_so_far' ++ [leak_bool true])
                              (myPos + (body1Length + 1) * 4) sp_val stackoffset body2 rt_so_far''
                              (fun t_so_far'' rt_so_far''' =>
                                 predictLE_with_prefix
                                   [ leak_Jal ]
                                   (fun rt_so_far'''' => rnext_stmt t_so_far'' myPos sp_val stackoffset s rt_so_far'''' f)
                                   rt_so_far'''))
                         rt_so_far'
                   | Some (qleak_bool false) =>
                       predictLE_with_prefix
                         [ leak_bcond_by_inverting cond (negb false) ]
                         (f (t_so_far' ++ [leak_bool false]))
                         rt_so_far'
                   | _ => None
                   end)
          | SSeq s1 s2 =>
              let s1Length := Z.of_nat (length (compile_stmt myPos stackoffset s1)) in
              rnext_stmt t_so_far myPos sp_val stackoffset s1 rt_so_far
                (fun t_so_far' rt_so_far' => rnext_stmt t_so_far' (myPos + 4 * s1Length) sp_val stackoffset s2 rt_so_far' f)
          | SSkip => f t_so_far rt_so_far
          | SCall resvars fname argvars =>
              match @map.get _ _ env e_env fname, @map.get _ _ _ e fname with
              | Some (params, rets, fbody), Some pos =>
                  predictLE_with_prefix
                    [ leak_Jal ](* jump to compiled function *)
                    (fun rt_so_far' => rnext_fun' rnext_stmt0 fuel' next t_so_far pos sp_val params rets fbody rt_so_far' f)
                    rt_so_far
              | _, _ => None
              end
          | SInteract _ _ _ =>
              predictLE_with_prefix
                leak_ext_call
                (f t_so_far)
                rt_so_far
          end
      end.

    Definition rnext_fun := rnext_fun' rnext_stmt.
  End WithOtherEnv.
  End WithEnv.

  

  (* compiles all functions just to obtain their code size *)
  Definition build_fun_pos_env(e_impl: env): pos_map :=
    (* since we pass map.empty as the fun_pos_env into compile_funs, the instrs
       returned don't jump to the right positions yet (they all jump to 42),
       but the instructions have the right size, so the posmap we return is correct *)
    snd (compile_funs map.empty e_impl).

End FlatToRiscv1.
