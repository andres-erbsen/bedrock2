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
  Context (width_big: 4 <= width). (*to avoid division by zero*)
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
                j = j + $1;
                coq:(cmd.unset "t")(*why? just because tailrec likes it?*)
              };
            i = i + $1;
            coq:(cmd.unset "j")
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
          KYBER_N = Z.of_nat (List.length a_coeffs_vals)->
          KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) ->
          @word.unsigned _ word (word.divu (word.of_Z KYBER_N) (word.of_Z 8)) <= KYBER_INDCPA_MSGBYTES ->
          WeakestPrecondition.call functions "poly_tomsg" k t m (msg :: a_coeffs :: nil)
            (fun (k' : trace) (T : io_trace) (M : mem) (rets : list word) =>
               T = t /\ rets = nil /\
                 exists k'',
                   k' = app k'' k /\ k'' = f msg a_coeffs KYBER_N).

    Require Import bedrock2.ZnWords.
    From coqutil.Macros Require Import symmetry.

    
    Lemma poly_tomsg_ok : program_logic_goal_for_function! poly_tomsg.
    Proof.
      repeat straightline. Check @Loops.tailrec.
      refine ((Loops.tailrec
                 (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                 (* program variables *) ("i" :: "a_coeffs" :: "msg" :: nil))%string
                (fun vi msg_vals a_coeffs_vals k t m i a_coeffs msg =>
                   PrimitivePair.pair.mk
                     (KYBER_N = Z.of_nat (List.length a_coeffs_vals) /\
                        KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) /\
                        ((array scalar8 (word.of_Z 1) msg msg_vals) * (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) * R)%sep m 
                       /\ vi = @word.unsigned _ word (word.divu (word.of_Z KYBER_N) (word.of_Z 8)) - word.unsigned i) (* precondition *)
                     (fun K T M I A_COEFFS MSG => (*postcondition*) 
                        T = t /\ A_COEFFS = a_coeffs /\ MSG = msg /\
                          exists MSG_VALS A_COEFFS_VALS,
                            KYBER_N = Z.of_nat (List.length A_COEFFS_VALS) /\
                              KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length MSG_VALS) /\
                            ((array scalar8 (word.of_Z 1) msg MSG_VALS) * (array scalar16 (word.of_Z 2) a_coeffs A_COEFFS_VALS) * R)%sep M
                )) 
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
        split.
        { repeat straightline.
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
          destruct (word.ltu x1 _) eqn:E.
          2: { rewrite word.unsigned_of_Z_0 in H4. exfalso. auto. }
          rewrite word.unsigned_ltu in E. apply Z.ltb_lt in E.
          assert (nsmall: (0 <= Z.to_nat (word.unsigned x1) < Datatypes.length x)%nat) by ZnWords.
          assert (Ex1: x1 = @word.of_Z _ word (@word.unsigned _ word (word.of_Z 1) * Z.of_nat (Z.to_nat (word.unsigned x1)))).
          { Search (Z.of_nat (Z.to_nat _)). rewrite Z2Nat.id.
            2: { assert (Hnonneg := word.unsigned_range x1 ). blia. }
            Search (word.unsigned _ * word.unsigned _). Search word.unsigned.
            apply word.unsigned_inj. Search (word.unsigned (word.of_Z _)).
            repeat rewrite word.unsigned_of_Z. cbv [word.wrap].
            Search ((_ mod _ * _) mod _).
            rewrite Z.mul_mod_idemp_l.
            2: { Search (_ ^ _ <> 0). apply word.modulus_nonzero. }
            assert (Hx1 := word.unsigned_range x1).
            Search (?a mod ?b = ?a). rewrite Z.mod_small; blia. }
          eapply Scalars.store_one_of_sep.
          { Check (array_address_inbounds ptsto (word.of_Z 1) x x3 (word.add x3 x1)). Search Init.Byte.byte.
            Check @array_index_nat_inbounds.
            seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x x3 (Z.to_nat (word.unsigned x1))) H3. Search x.
            { ZnWords. }
            
            rewrite <- Ex1 in H3.
            ecancel_assumption. }
          repeat straightline. (* neat, why did that work now? *)
          refine ((Loops.tailrec
                     (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                     (* program variables *) ("j" :: "i" :: "a_coeffs" :: "msg" :: nil))%string
                    (fun vj msg_vals a_coeffs_vals k t m j i a_coeffs msg =>
                       PrimitivePair.pair.mk
                         (KYBER_N = Z.of_nat (List.length a_coeffs_vals) /\
                            KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) /\
                            i = x1(*value of i before we enter loop*) /\
                            ((array scalar8 (word.of_Z 1) msg msg_vals) * (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) * R)%sep m 
                          /\ vj = word.wrap 8 - word.unsigned j) (* precondition *)
                         (fun K T M J I A_COEFFS MSG => (*postcondition*) 
                            T = t /\ A_COEFFS = a_coeffs /\ MSG = msg /\
                              exists MSG_VALS A_COEFFS_VALS,
                                KYBER_N = Z.of_nat (List.length A_COEFFS_VALS) /\
                                  KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length MSG_VALS) /\
                            ((array scalar8 (word.of_Z 1) msg MSG_VALS) * (array scalar16 (word.of_Z 2) a_coeffs A_COEFFS_VALS) * R)%sep M
                    )) 
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
          { Check array_index_nat_inbounds. Search (Lift1Prop.iff1 (sep _ _) (sep _ _)).
            seprewrite_in (symmetry! @array_cons) H5.
            seprewrite_in @sep_comm H5.
            remember (Z.to_nat (word.unsigned x1)) as n eqn:En.
            Check array_append.
            rewrite Ex1 in H5.
            replace (Z.of_nat n) with (Z.of_nat (List.length (List.firstn n x))) in H5.
            2: { rewrite List.firstn_length. blia. }
            seprewrite_in (symmetry! @array_append) H5. subst.
            split; [|split; [|split; [|split] ] ].
            4: ecancel_assumption.
            { assumption. }
            { repeat rewrite List.app_length. cbn [List.length].
              rewrite List.firstn_length. rewrite List.skipn_length. blia. }
            { reflexivity. }
            { reflexivity. } }
          { repeat straightline. eexists. eexists. split.
            { repeat straightline. eexists. split.
              { subst localsmap. cbv [reconstruct].
                cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                Search (map.get (map.put _)). Search map.get. rewrite map.get_put_same.
                reflexivity. }
              repeat straightline. }
            split.
            { repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { subst localsmap. cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  Search (map.get (map.put _)). Search map.get. rewrite map.get_put_diff by congruence.
                  rewrite map.get_put_diff by congruence. rewrite map.get_put_same. reflexivity. }
                repeat straightline. eexists. split.
                { subst localsmap. cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  Search (map.get (map.put _)). Search map.get. rewrite map.get_put_diff by congruence.
                  rewrite map.get_put_same. reflexivity. }
                repeat straightline. eexists. split.
                { subst localsmap. cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  rewrite map.get_put_same. reflexivity. }
                repeat straightline.
                destruct (word.ltu _ _) eqn:Ex6.
                2: { rewrite word.unsigned_of_Z_0 in H10. exfalso. auto. }
                rewrite word.unsigned_ltu in Ex6. apply Z.ltb_lt in Ex6.
                eexists. split.
                { eapply load_two_of_sep. Search load. repeat straightline.
                  remember (word.add (word.mul v3 x1) x6) as n eqn:En.
                  seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ scalar16 (word.of_Z 2) (word.of_Z 0) x5 x8 (Z.to_nat (word.unsigned n))) H11.
                  2: { repeat straightline. use_sep_assumption. cancel.
                       cancel_seps_at_indices 1%nat 0%nat.
                       { f_equal. f_equal. subst v0 n. Search (Z.of_nat (Z.to_nat _)).
                         rewrite Z2Nat.id.
                         2: { Search word.unsigned.
                              assert (Hnonneg:= word.unsigned_range (word.add (word.mul v3 x1) x6)).
                              blia. }
                         ZnWords. (*interesting, why did this not work before Z2Nat.id?*) }
                       ecancel_done. }
                  (*ZnWords hangs here.*)
                  subst. subst v3. subst v0. Search (Z.to_nat _ < Z.to_nat _)%nat.
                  assert (Hnonneg := word.unsigned_range (word.add (word.mul (word.of_Z 8) x1) x6)).
                  enough ((word.unsigned (word.add (word.mul (word.of_Z 8) x1) x6)) < KYBER_N).
                  { Search KYBER_N. subst KYBER_N. Search a_coeffs_vals. blia. }
                  Search word.divu. Search word.unsigned (word.add _ _).
                  assert (0 < word.unsigned (word:=word) (word.of_Z 8)).
                  { rewrite word.unsigned_of_Z. cbv [word.wrap]. Search (_ mod _).
                    rewrite Z.mod_small; try split; try blia. Search (_ ^ _ <= _ ^ _).
                    assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                    blia. } Search word.divu.
                  assert (0 < 2 ^ width).
                  { Search (0 < _ ^ _). apply Z.pow_pos_nonneg; blia. }
                  rewrite word.unsigned_add, word.unsigned_mul, word.unsigned_divu in * by blia.
                  rewrite word.unsigned_of_Z in E. cbv [word.wrap] in *.
                  Search ((_ mod _ / _) mod _). Search ((_ mod _ + _) mod _).
                  rewrite Z.add_mod_idemp_l by blia. rewrite word.unsigned_of_Z in *. Search word.divu.
                  assert (word.unsigned x1 < KYBER_N mod 2 ^ width / word.wrap 8).
                  { eapply Z.lt_le_trans. 1: eassumption.
                    Search (_ mod _ <= _). apply Z.mod_le; try blia. Search word.divu.
                    Search (0 <= _ / _). apply Z_div_nonneg_nonneg; try blia.
                    Search (0 <= _ mod _). apply Z_mod_nonneg_nonneg; blia. }
                  enough ((word.wrap 8 * word.unsigned x1 + word.unsigned x6) < KYBER_N).
                  { eapply Z.le_lt_trans. 2: eassumption. apply Z.mod_le; try blia.
                    assert (Hx6 := word.unsigned_range x6). assert (Hx1 := word.unsigned_range x1).
                    blia. }
                  assert (word.unsigned x1 < KYBER_N / word.wrap 8).
                  { eapply Z.lt_le_trans. 1: eassumption. Search (_ / _ <= _ / _)%Z.
                    apply Z.div_le_mono; try blia. apply Z.mod_le; blia. }
                  enough (word.wrap 8 * (word.unsigned x1 + 1) <= KYBER_N).
                  { blia. }
                  assert (word.unsigned x1 + 1 <= KYBER_N / word.wrap 8) by blia.
                  Search (_ * _ <= _ * _). apply Zmult_le_compat_l with (p := word.wrap 8) in H15; try blia.
                  eapply Z.le_trans. 1: eassumption. Search (_ * (_ / _) <= _).
                  apply Z.mul_div_le. blia. }
                eauto. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l. rewrite map.get_put_same. reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l0. rewrite map.get_put_same. reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l1. rewrite map.get_put_same. reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l2. rewrite map.get_put_same. reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l3. rewrite map.get_put_same. reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. eexists. split.
                { subst l4 l3 l2 l1 l0 l localsmap. eapply Scalars.load_one_of_sep.
                  seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x4 x9 (Z.to_nat (word.unsigned x1))) H11.
                  { ZnWords. }
                  rewrite <- Ex1 in H11.
                  ecancel_assumption. }
                repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  rewrite map.get_put_same. reflexivity. }
                repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. }
              eapply Scalars.store_one_of_sep.
              { seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x4 x9 (Z.to_nat (word.unsigned x1))) H11.
                { ZnWords. }
                rewrite <- Ex1 in H11. ecancel_assumption. }
              repeat straightline. eexists. eexists. split.
              { repeat straightline. eexists. split.
                { repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
                  repeat rewrite map.get_put_diff by congruence.
                  cbv [reconstruct].
                  cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
                  repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                  reflexivity. }
                repeat straightline. }
              repeat straightline.
              do 4 eexists. Print enforce. Print gather. split.
              { Print enforce. repeat straightline. Print Loops.enforce. cbv [Loops.enforce]; cbn.
                subst l6 l5 l4 l3 l2 l1 l0 l localsmap.
                repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
                { exact eq_refl. }
                { eapply map.map_ext; intros k0.
                  repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
                  repeat (destruct String.eqb; trivial). } }
              seprewrite_in (symmetry! @array_cons) H12.
              remember (Byte.byte.of_Z (word.unsigned (word.or _ _))) as something.
              seprewrite_in @sep_comm H12.
              remember (Z.to_nat (word.unsigned x1)) as n eqn:En.
              Check array_append.
              rewrite Ex1 in H12.
              replace (Z.of_nat n) with (Z.of_nat (List.length (List.firstn n x4))) in H12.
              2: { rewrite List.firstn_length. blia. }
              seprewrite_in (symmetry! @array_append) H12. subst.
              destruct (word.ltu x6 (word.of_Z 8)) eqn:Ex6.
              2: { rewrite word.unsigned_of_Z_0 in H10. exfalso. auto. }
              rewrite word.unsigned_ltu in Ex6. apply Z.ltb_lt in Ex6.
              assert (8 < 2 ^ width).
              { assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                blia. }
              rewrite word.unsigned_of_Z in Ex6. cbv [word.wrap] in *.
              rewrite Z.mod_small in * by blia.
              eexists. eexists. eexists. repeat split.
              3: ecancel_assumption.
              all: intuition eauto.
              { repeat rewrite List.app_length. cbn [Datatypes.length].
                rewrite List.firstn_length. rewrite List.skipn_length. blia. }
              { subst l6 l5 l4 l3 l2 l1 l0 l localsmap. rewrite word.unsigned_add.
                clear H12. cbv [word.wrap]. rewrite word.unsigned_of_Z. cbv [word.wrap].
                rewrite (Z.mod_small 1) by blia.
                enough ((word.unsigned x6 + 1) mod 2 ^ width <= word.unsigned x6 + 1).
                { blia. }
                apply Z.mod_le; try blia. assert (sth:= word.unsigned_range x6). blia. }
              { subst l6 l5 l4 l3 l2 l1 l0 l localsmap. rewrite word.unsigned_add.
                clear H12. subst v0. rewrite word.unsigned_of_Z.
                cbv [word.wrap]. rewrite (Z.mod_small 1) by blia. rewrite (Z.mod_small 8) by blia.
                rewrite Z.mod_small.
                { blia. }
                pose proof (word.unsigned_range x6). blia. } }
            (*postcondition?*)
            { intros. intuition. eexists. eexists. split; [|split]. 3: ecancel_assumption.
              all: auto.
          } }
          repeat straightline. eexists. eexists. split.
          { repeat straightline. eexists. split.
            { cbv [reconstruct].
              cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
              repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                reflexivity. }
            repeat straightline. }
          repeat straightline. eexists. eexists. eexists. split.
          { cbv [Loops.enforce]; cbn.
            subst l l0.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
            { exact eq_refl. }
            { eapply map.map_ext; intros k0.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          (*postcondition*)
          repeat straightline.
          eexists. eexists. eexists. split.
          { split; [|split; [|split] ].
            3: ecancel_assumption.
            all: eauto.
            3: { repeat straightline. Unshelve.
                 4: { exact ((List.firstn (Z.to_nat (word.unsigned x1)) x ++
                                Byte.byte.of_Z (word.unsigned (word.of_Z (word:=word)0))
                                :: List.skipn (S (Z.to_nat (word.unsigned x1))) x))%list. }
                 4: exact x0.
                 1: { speecancel_assumption.
                      1: ecancel_assumption. shelve. ecancel_assumption. instantiate (1 := (List.firstn (Z.to_nat (word.unsigned x1)) x ++
           Byte.byte.of_Z (word.unsigned (word.of_Z 0))
           :: List.skipn (S (Z.to_nat (word.unsigned x1))) x)%list). eapply H5. ecancel_assumption.
          repeat split.
        repeat split. 3: ecancel_assumption.
        
        eexists. eexists. eexists. split.
        3: {
          cbv [reconstruct].
            rewrite word.unsigned_add. clear H12. subst ZnWords.
            blia.
            rewrite 
            2: { split; [blia|].
                 assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                 blia. }
            
            by blia.
            ZnWords.
            ZnWords. }
          simpl.
          all: try ZnWords.
          repeat split. 3: ecancel_assumption.
          eexists. eexists. eexists. repeat split.
          3: {
          6: {          { 
          repeat straightline.
          seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x4 x9 (Z.to_nat (word.unsigned x1))) H11.
              subst. rewrite ecancel_assumption.
              repeat straightline. subst l4 l3 l2 l1 l0 l localsmap.
              repeat rewrite map.get_put_diff by congruence.
              cbv [reconstruct].
              cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
              repeat rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
              reflexivity. }
          }
          repeat straightline. eexists. eexists. split.
          { repeat straightline. eexists. split.
            { repeat straightline. subst l4. rewrite map.get_put_same. reflexivity. }
            repeat straightline. }
            repeat straightline. }
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same.
            reflexivity. }
          repeat straightline. eexists. split.
          { subst localsmap. cbv [reconstruct].
            cbn [HList.tuple.of_list]. cbv [map.putmany_of_tuple]. simpl.
            rewrite map.get_put_same. reflexivity. }
          eauto. }
          { repeat straightline.
              clear -H14. blia.
              
                2: { blia.
                { 
              Z.div_mod_to_equations. blia. blia. ZnWords. enough (0 < 2 ^ width).
              { Z.div_mod_to_equations. ZnWords. blia. clear H1 H2 H3.
              blia.
              ZnWords.
              word.unsigned_mul. ZnWords.
              ZnWords.
              apply Z2Nat.inj_lt. blia.
              Check Z2Nat.inj_lt.
              { assert .
                blia. }
              { ZnWords. blia.
              ZnWords.
              ZnWords.
                     . subst v3. subst. subst v1. subst v2.
                                            Search word.unsigned.  ZnWords. subst v0 n. remember (word.mul _ _) as X. ZnWords. f_equal. 
                   cancel_seps_at_indices 0%nat 0%nat. cancel. cancel. cancel. cancel. ecancel_assumption.
            intros.
          split; [|split; [|split] ].
          3: { subst. Unshelve. 4: { exact ((List.firstn n x ++ Byte.byte.of_Z (word.unsigned v1) :: List.skipn (S n) x)%list). seprewrite @sep_assoc. H7. eapply H7. ecancel_assumption.
          replace x1 with (@word.of_Z _ word (@word.unsigned _ word (word.of_Z 1) * Z.of_nat (Datatypes.length (List.firstn n x)))) in H7.
          2: { rewrite List.firstn_length. replace (Init.Nat.min n (Datatypes.length x)) with n by blia.
               subst. ZnWords.
          { 
          forget 4 as x.
          replace x1 with (word.of_Z (word.unsigned size * Z.of_nat (Datatypes.length xs)))
          seprewrite_in @sep_assoc H7.
          seprewrite_in (symmetry! @array_append) H7.
          Check array_index_nat_inbounds.
          seprewrite_in @sep_assoc H7.
          seprewrite_in @sep_assoc H7. seprewrite_in @sep_assoc H7.
          remember (Z.to_nat (word.unsigned x1)) as n eqn:En.
          remember (List.firstn n x ++ (Byte.byte.of_Z (word.unsigned v1)) :: List.skipn (S n) x)%list as x' eqn:Ex'.
          Check array_index_nat_inbounds.
          replace (Byte.byte.of_Z (word.unsigned v1)) with (List.hd Byte.x00 (List.skipn n x')) in H7.
          2: { subst. rewrite List.skipn_app_r.
               { reflexivity. }
               Search (Datatypes.length (List.firstn _ _)).
               rewrite List.firstn_length. blia. }
          seprewrite_in (symmetry! @array_cons) H7. Search array.
          seprewrite_in (symmetry! @array_append) H7.
          replace (List.firstn n x) with (List.firstn n x') in H7.
          
          2: { 
               Search (length x).
               Search x. Search KYBER_INDCPA_MSGBYTES.
          Check sep_assoc.
          Search (list _ -> list _).
          seprewrite_in (symmetry! @array_index_nat_inbounds) H7.  _ _ _ _ _ _ _ ptsto (word.of_Z 1) Byte.x00 x x3 (Z.to_nat (word.unsigned x1))) H7. (*have to do something nontrivial here; seprewrite the other way.*) repeat (straightline || intuition eauto). straightline. }
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
