Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition div3329_vartime := func! (x) ~> ret {
  ret = $(expr.op bopname.divu "x" 3329)
}.

Definition div3329 := func! (x) ~> ret {
  ret = (x * $989558401) >> $32;
  ret = (ret + (x - ret >> $1)) >> $11
}.

From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Import Interface.word Coq.Lists.List List.ListNotations.
From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
Import ProgramLogic.Coercions.

Instance ctspec_of_div3329 : spec_of "div3329" :=
  fun functions => forall k, exists k_, forall t m x,
      WeakestPrecondition.call functions "div3329" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = k_
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_ct : program_logic_goal_for_function! div3329.
Proof.
  repeat (straightline || eexists).
  { (* no leakag -- 3 minutes *) cbv [k' k'0]. cbn. exact eq_refl. }
Qed.

Instance vtspec_of_div3329 : spec_of "div3329_vartime" :=
  fun functions => forall k, forall t m x,
      WeakestPrecondition.call functions "div3329_vartime" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = [leak_word (word.of_Z 3329); leak_word x]++k
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_vt : program_logic_goal_for_function! div3329_vartime.
Proof.
  repeat (straightline || eexists).
Qed.
