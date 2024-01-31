(*https://github.com/pq-crystals/kyber/commit/dda29cc63af721981ee2c831cf00822e69be3220*)
(*
typedef struct{
  int16_t coeffs[KYBER_N];
} poly;

void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *a)
{
  unsigned int i,j;
  uint32_t t;

  for(i=0;i<KYBER_N/8;i++) {
    msg[i] = 0;
    for(j=0;j<8;j++) {
      t  = a->coeffs[8*i+j];
      // t += ((int16_t)t >> 15) & KYBER_Q;
      // t  = (((t << 1) + KYBER_Q/2)/KYBER_Q) & 1;
      t <<= 1;
      t += 1665;
      t *= 80635;
      t >>= 28;
      t &= 1;
      msg[i] |= t << j;
    }
  }
}
 *)

Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Map.SeparationLogic Array Scalars Loops.


From coqutil Require Import Datatypes.List Word.Bitwidth Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics Syntax.
Import coqutil.Word.Properties coqutil.Map.Properties.

Require Import bedrock2.AbsintWordToZ.

Infix "/" := (expr.op bopname.divu) (in custom bedrock_expr at level 5, left associativity).

Section WithWord.
  Context {width: Z} {BW: Bitwidth width}. (*{word: word.word w*)
  Context {word: word.word width}.
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env : map.map string (list string * list string * cmd)}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.
  Context (KYBER_N KYBER_Q KYBER_INDCPA_MSGBYTES : Z).
  (* ^is this how to do global constants in bedrock2? *) Print expr.expr.
  
  Definition poly_tomsg :=
    func! (msg, a_coeffs) {
        i = $0;
        while (i < coq:(expr.literal KYBER_N) / $8) {
            store1(msg + i, $0);
            j = $0;
            while (j < $8) {
                t = load2(a_coeffs + $2 (* <- because 2-byte array *) * ($8 * i + j));
                t = t << $1;
                t = t + $1665;
                t = t * $80635;
                t = t >> $28;
                t = t & $1;
                store1(msg + i, load1(msg + i) | (t << j));
                j = j + $1
              };
            i = i + $1
          }
      }.
  
  (*Definition bad_poly_tomsg :=
    func! (msg, a_coeffs) {
        i = $0;
        while (i < KYBER_N / $8) {
            store1(msg + i, $0);
            j = $0;
            while (j < $8) {
                t = load2(a_coeffs + $2 (* <- because 2-byte array *) * ($8 * i + j));
                (* t += ((int16_t)t >> 15) & KYBER_Q;
                   ^ want to implement that.  t is a uint16_t.
                   apparently uint -> int casts are implementation-defined when not in range.
                   how confusing.
                   so we should assume that t is in int16_t range.
                   But then ((int16_t) >> 15) = 0, and the whole thing is a no-op.
                   So what?
                   I suppose we just assume the cast just does nothing (aside from changing the type),
                   regardless of the value of t.  That's the only thing that makes that line of code 
                   reasonable.
                 *)
                j = j + $1
              };
            i = i + $1
          }
      }.*)

    Instance poly_tomsg_ct : spec_of "poly_tomsg" :=
      fun functions =>
        exists f : word -> word -> Z -> trace,
        forall (k : trace) (t : io_trace) (m : mem) (msg a_coeffs : word) (msg_vals : list Byte.byte) (a_coeffs_vals : list word) (R : mem -> Prop),
          ((array scalar8 (word.of_Z 1) msg msg_vals) ⋆ (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) ⋆ R)%sep m ->
          List.length a_coeffs_vals = Z.to_nat KYBER_N ->
          List.length msg_vals = Z.to_nat KYBER_INDCPA_MSGBYTES ->
          @word.unsigned _ word (word.divu (word.of_Z KYBER_N) (word.of_Z 8)) <= KYBER_INDCPA_MSGBYTES ->
          WeakestPrecondition.call functions "poly_tomsg" k t m (msg :: a_coeffs :: nil)
            (fun (k' : trace) (T : io_trace) (M : mem) (rets : list word) =>
               T = t /\ rets = nil /\
                 exists k'',
                   k' = app k'' k /\ k'' = f msg a_coeffs KYBER_N).

    Require Import bedrock2.ZnWords.

    
    Lemma poly_tomsg_ok : program_logic_goal_for_function! poly_tomsg.
    Proof.
      repeat straightline. Check @Loops.tailrec.
      refine ((Loops.tailrec
                 (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                 (* program variables *) ("i" :: "a_coeffs" :: "msg" :: nil))%string
                (fun vi msg_vals a_coeffs_vals k t m i a_coeffs msg =>
                   PrimitivePair.pair.mk
                     (List.length a_coeffs_vals = Z.to_nat KYBER_N /\
                      List.length msg_vals = Z.to_nat KYBER_INDCPA_MSGBYTES /\
                        ((array scalar8 (word.of_Z 1) msg msg_vals) * (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) * R)%sep m 
                       /\ vi = @word.unsigned _ word (word.divu (word.of_Z KYBER_N) (word.of_Z 8)) - word.unsigned i) (* precondition *)
                     (fun K T M I A_COEFFS MSG => (*postcondition*) 
                        T = t /\ A_COEFFS = a_coeffs /\ MSG = msg)) 
                (fun n m => 0 <= n < m) (* well_founded relation *)
                _ _ _ _ _ _ _);
        cbn [HList.hlist.foralls HList.tuple.foralls
               HList.hlist.existss HList.tuple.existss
               HList.hlist.apply  HList.tuple.apply
               HList.hlist
               List.repeat Datatypes.length
               HList.polymorphic_list.repeat HList.polymorphic_list.length
               PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
      { cbv [Loops.enforce]; cbn.
          subst l l0.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
          { exact eq_refl. }
          { eapply map.map_ext; intros k0.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
      { exact (Z.lt_wf _). }
      { repeat (straightline || intuition eauto). }
      { repeat straightline.
        eexists. eexists. split.
        { repeat straightline. eexists. split.
          { repeat straightline. subst localsmap. cbv [reconstruct].
            cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
            Search (map.get (map.put _)). Search map.get. rewrite map.get_put_same.
            reflexivity. (* why will straightline not do that for me??
                            it would earlier, but then I changed some context variables. *) }
          repeat straightline. }
        repeat straightline.
        split. 2: auto.
        repeat straightline.
        eexists. eexists. split.
        { repeat straightline. eexists. split.
          { repeat straightline. subst localsmap. cbv [reconstruct].
            cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
            rewrite map.get_put_diff by congruence. rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same.
            reflexivity. }
          repeat straightline. eexists. split.
          { subst localsmap. cbv [reconstruct].
            cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
            rewrite map.get_put_same. reflexivity. }
          eauto. }
        repeat straightline.
        (*finally we do something interesting*)
        eapply Scalars.store_one_of_sep.
        { Check (array_address_inbounds ptsto (word.of_Z 1) x x3 (word.add x3 x1)). Search Init.Byte.byte.
          destruct (word.ltu x1 _) eqn:E.
          2: { rewrite word.unsigned_of_Z_0 in H6. exfalso. auto. }
          rewrite word.unsigned_ltu in E. apply Z.ltb_lt in E.
          Check @array_index_nat_inbounds.
          eassert (H5' := H5).
          seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x x3 (Z.to_nat (word.unsigned x1))) H5. Search x.
          { ZnWords. }
          replace (@word.of_Z _ word (@word.unsigned _ word (word.of_Z 1) * Z.of_nat (Z.to_nat (word.unsigned x1)))) with x1 in *.
          2: { Search (Z.of_nat (Z.to_nat _)). rewrite Z2Nat.id.
               2: { assert (Hnonneg := word.unsigned_range x1 ). blia. }
               Search (word.unsigned _ * word.unsigned _). Search word.unsigned.
               apply word.unsigned_inj. Search (word.unsigned (word.of_Z _)).
               repeat rewrite word.unsigned_of_Z. cbv [word.wrap].
               Search ((_ mod _ * _) mod _).
               rewrite Z.mul_mod_idemp_l.
               2: { Search (_ ^ _ <> 0). apply word.modulus_nonzero. }
               assert (Hx1 := word.unsigned_range x1).
               Search (?a mod ?b = ?a). rewrite Z.mod_small; blia. }
          ecancel_assumption. }
        repeat straightline. (* neat, why did that work now? *)
        refine ((Loops.tailrec
                 (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                   (* program variables *) ("j" :: "i" :: "a_coeffs" :: "msg" :: nil))%string
                (fun vj msg_vals a_coeffs_vals k t m j i a_coeffs msg =>
                   PrimitivePair.pair.mk
                     (List.length a_coeffs_vals = Z.to_nat KYBER_N /\
                      List.length msg_vals = Z.to_nat KYBER_INDCPA_MSGBYTES /\
                        ((array scalar8 (word.of_Z 1) msg msg_vals) * (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) * R)%sep m 
                       /\ vj = word.wrap 8 - word.unsigned j) (* precondition *)
                     (fun K T M J I A_COEFFS MSG => (*postcondition*) 
                        T = t /\ A_COEFFS = a_coeffs /\ MSG = msg)) 
                (fun n m => 0 <= n < m) (* well_founded relation *)
                _ _ _ _ _ _ _);
        cbn [HList.hlist.foralls HList.tuple.foralls
               HList.hlist.existss HList.tuple.existss
               HList.hlist.apply  HList.tuple.apply
               HList.hlist
               List.repeat Datatypes.length
               HList.polymorphic_list.repeat HList.polymorphic_list.length
               PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
        { cbv [Loops.enforce]; cbn.
          subst l.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
          { exact eq_refl. }
          { eapply map.map_ext; intros k0.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        { exact (Z.lt_wf _). }
        { (*have to do something nontrivial here; seprewrite the other way.*) repeat (straightline || intuition eauto). straightline. }
               { blia. }
               { blia.
                 { 
               Search ord.unsigned.
               ZnWords.
               cbv [word.of_Z]. rewrite <- word.unsigned_mul.

               rewrite Z2Nat.inj_le. rite Z.of_nat_inj. ZnWords.
            2: { Search (Z.to_nat _ <= Z.to_nat _)%nat. apply Z2Nat.inj_le.
                 3: { 
            { eassumption.
            rewrite word.word_sub_add_l_same_l. ZnWords. }
          { rewrite word.word_sub_add_l_same_l. Search (_ mod 1). rewrite word.unsigned_of_Z.
            cbv [word.wrap]. Search array. Search (_ mod (_ mod _)). apply Z.mod_1_r. ZnWords.
          
            rewrite H4. clear H4. ZnWords. rewrite Z2Nat.id. ZnWords.
            2: { Search word.unsigned.
                 assert (Hnonneg := word.unsigned_range (word.divu (word.of_Z KYBER_N) (word.of_Z 8)) ).
                 blia. }
            Search word.unsigned. ZnWords.
            remember (word.divu _ _) as z eqn:Heqz.
            rewrite word.unsigned_of_Z in *. cbv [word.wrap] in *. Search (1 mod _).
            ZnWords. }
            clear Heqz. Search word.wrap. Print word.wrap. Check array_address_inbounds.
            (*this is not nice. maybe try writing tailrec as in memequal, where we ignore the part of *)
             blia.
            Search word.divu. blia. 
            simpl in E. rewrite word.of_Z_unsigned in E. slia.
            discriminate H4. destruct H4. congruence.
            Search (word.unsigned (word.of_Z _)).
            blia.
          4: {
        fold (@word.unsigned _ word).
        econstructor. split.
        { Check Scalars.store_one_of_sep.
        straightline. eexists. eexists. split.
        { repeat straightline.
      refine (
          tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
            (fun l xs R k t m left right target =>
               PrimitivePair.pair.mk
                 (sep (array scalar (word.of_Z 8) left xs) R m /\
                    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                    List.length xs = l)
                 (fun        K T M LEFT RIGHT TARGET => T = t /\ sep (array scalar (word.of_Z 8) left xs) R M))
            lt _ _ _ _ _ _ _)
               
Print bsearch.

(*Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R k t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string k t m (left::right::target::nil)%list
      (fun k' t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).*)
