Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Simp.
Require Import compiler.UniqueSepLog.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface.
Require Import compiler.FlatImp.
Require Import coqutil.Datatypes.HList.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Module exec.
  Section FlatImpExec.
    Context {varname: Type} {varname_eqb: varname -> varname -> bool}.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
    Context {mem: map.map word byte} {locals: map.map varname word}
            {env: map.map String.string (list varname * list varname * stmt varname)}.
    Context {ext_spec: ExtSpec}.
    Context {varname_eq_spec: EqDecider varname_eqb}
            {word_ok: word.ok word}
            {mem_ok: map.ok mem}
            {locals_ok: map.ok locals}
            {env_ok: map.ok env}
            {ext_spec_ok: ext_spec.ok ext_spec}.
    Variable (e: env).

    Local Notation metrics := MetricLog.

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop.

    Definition lookup_op_locals (l: locals) (o: operand) :=
      match o with
      | Var vo => map.get l vo
      | Const co => Some (word.of_Z co)
      end.

    Inductive exec:
      stmt varname ->
      trace -> io_trace -> mem -> locals -> metrics ->
      (trace -> io_trace -> mem -> locals -> metrics -> Prop)
    -> Prop :=

    | interact: forall k t m Keep mGive l mc action argvars argvals resvars outcome post,
        (Keep \*/ Some mGive) = Some m ->
        map.getmany_of_list l argvars = Some argvals ->
        ext_spec t mGive action argvals outcome ->
        (forall mReceive resvals klist,
            outcome mReceive resvals klist ->
            exists l', map.putmany_of_list_zip resvars resvals l = Some l' /\
            forall m', (Keep \*/ Some mReceive) = Some m' ->
            post (leak_list klist :: k) (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (addMetricInstructions 1
                 (addMetricStores 1
                 (addMetricLoads 2 mc)))) ->
        exec (SInteract resvars action argvars) k t m l mc post

    | call: forall k t m l mc binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody (leak_unit :: k) t m st0 mc outcome ->
        (forall k' t' m' mc' st1,
            outcome k' t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post k' t' m' l' mc') ->
        exec (SCall binds fname args) k t m l mc post

    | load: forall k t m l mc sz R x a o v addr post,
        map.get l a = Some addr ->
        R \*/ one sz (word.add addr (word.of_Z o)) v = Some m ->
        post (leak_word (word.add addr (word.of_Z o)) :: k) t m (map.put l x v)
             (addMetricLoads 2
             (addMetricInstructions 1 mc)) ->
        exec (SLoad sz x a o) k t m l mc post

    | store: forall k t m mc l sz a o addr v old_val val R post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        R \*/ one sz (word.add addr (word.of_Z o)) old_val = Some m ->
        post (leak_word (word.add addr (word.of_Z o)) :: k) t (mmap.force (R \*/ one sz (word.add addr (word.of_Z o)) val)) l
             (addMetricLoads 1
             (addMetricInstructions 1
             (addMetricStores 1 mc))) ->
        exec (SStore sz a v o) k t m l mc post

    | stackalloc: forall k t mSmall l mc x n body post,
        n mod (bytes_per_word width) = 0 ->
        (forall (a: word) (oldstackbytes: tuple byte (Z.to_nat n)) (mCombined: mem),
            bytes a oldstackbytes \*/ Some mSmall = Some mCombined ->
            exec body (consume_word a :: k) t mCombined (map.put l x a) (addMetricLoads 1 (addMetricInstructions 1 mc))
                 (fun k' t' mCombined' l' mc' =>
                    exists (mSmall': mem) (newstackbytes: tuple byte (Z.to_nat n)),
                      Some mSmall' \*/ bytes a newstackbytes = Some mCombined' /\
                      post k' t' mSmall' l' mc')) ->
        exec (SStackalloc x n body) k t mSmall l mc post

    | lit: forall k t m l mc x v post,
        post k t m (map.put l x (word.of_Z v))
             (addMetricLoads 8
             (addMetricInstructions 8 mc)) ->
        exec (SLit x v) k t m l mc post
    | op: forall k t m l mc x op y y' z z' post,
        map.get l y = Some y' ->
        lookup_op_locals l z = Some z' ->
        post (leak_binop op y' z' ++ k) t m (map.put l x (interp_binop op y' z'))
             (addMetricLoads 2
             (addMetricInstructions 2 mc)) ->
        exec (SOp x op y z) k t m l mc post
    | set: forall k t m l mc x y y' post,
        map.get l y = Some y' ->
        post k t m (map.put l x y')
             (addMetricLoads 1
             (addMetricInstructions 1 mc)) ->
        exec (SSet x y) k t m l mc post
    | if_true: forall k t m l mc cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen (leak_bool true :: k) t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) k t m l mc post
    | if_false: forall k t m l mc cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse (leak_bool false :: k) t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) k t m l mc post
    | loop: forall k t m l mc cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 k t m l mc mid1 ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond <> None) ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond = Some false ->
            post (leak_bool false :: k') t' m' l'
                 (addMetricLoads 1
                 (addMetricInstructions 1
                 (addMetricJumps 1 mc')))) ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond = Some true ->
            exec body2 (leak_bool true :: k') t' m' l' mc' mid2) ->
        (forall k'' t'' m'' l'' mc'',
            mid2 k'' t'' m'' l'' mc'' ->
            exec (SLoop body1 cond body2) k'' t'' m'' l''
                 (addMetricLoads 2
                 (addMetricInstructions 2
                 (addMetricJumps 1 mc''))) post) ->
        exec (SLoop body1 cond body2) k t m l mc post
    | seq: forall k t m l mc s1 s2 mid post,
        exec s1 k t m l mc mid ->
        (forall k' t' m' l' mc', mid k' t' m' l' mc' -> exec s2 k' t' m' l' mc' post) ->
        exec (SSeq s1 s2) k t m l mc post
    | skip: forall k t m l mc post,
        post k t m l mc ->
        exec SSkip k t m l mc post.

  End FlatImpExec.
End exec.
Notation exec := exec.exec.
