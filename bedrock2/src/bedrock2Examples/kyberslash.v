(*https://github.com/pq-crystals/kyber/commit/dda29cc63af721981ee2c831cf00822e69be3220*)
(*
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

Require Import Coq.ZArith.BinInt Coq.Strings.String Coq.Lists.List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.sanity.

Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope string_scope.

Definition poly_tomsg :=
  func! (msg, a) {
      i = $0;
      while (i < KYBER_N >> $3 (*could not figure out how to type /.  Also, optimization?*)) {
          
          i = i + $1
        }
    }.

(*Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R k t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string k t m (left::right::target::nil)%list
      (fun k' t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).*)
