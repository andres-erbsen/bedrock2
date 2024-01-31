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

Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import Coq.ZArith.BinInt Coq.Strings.String Coq.Lists.List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.sanity.

Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Require Import bedrock2.Syntax.
Import Syntax.bopname. Print expr.expr. Print mul.

Infix "/" := (expr.op divu) (in custom bedrock_expr at level 5, left associativity).

Section WithWord.
  (*Context {width: Z}{BW: Bitwidth width}{word: word.word width}.*)
  Context {word: word.word 32}.
  Context (KYBER_N KYBER_Q : word).
  (* ^is this how to do global constants in bedrock2? *)
  
  Definition poly_tomsg :=
    func! (msg, a_coeffs) {
        i = $0;
        while (i < KYBER_N / $8) {
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
  
  Definition bad_poly_tomsg :=
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
      }.

  Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

  Import Syntax BinInt String List.ListNotations.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  

  Require Import bedrock2.WeakestPrecondition.
  Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
  Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
  From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Array Scalars Loops.

  
  Require Import bedrock2.WeakestPreconditionProperties.
  From coqutil.Tactics Require Import Tactics letexists eabstract.
  Require Import bedrock2.ProgramLogic bedrock2.Scalars.
  Require Import coqutil.Word.Interface.
  
  Section WithParameters.
    Context {mem: map.map word Byte.byte}.
    Context {word_ok: word.ok word} {mem_ok: map.ok mem}. Print array. Print ptsto. Print scalar16. Print ptsto.
  
    Definition poly_tomsg_ct : spec_of "poly_tomsg" :=
      fun functions =>
        exists f : word -> word -> trace,
        forall (k : trace) (t : io_trace) (m : mem) (msg a_coeffs : word) (msg_vals : list Byte.byte) (a_coeffs_vals : list word) (R : mem -> Prop),
          ((array scalar8 (word.of_Z 1) msg msg_vals) ⋆ (array scalar16 (word.of_Z 2) a_coeffs a_coeffs_vals) ⋆ R)%sep m ->
          True.
    (*(scalar a_addr a ⋆ scalar b_addr b ⋆ R)%sep m ->
          call functions "swap" k t m [a_addr; b_addr]
            (fun (k' : trace) (T : io_trace) (M : mem) (rets : list word) =>
               M =* scalar a_addr b * scalar b_addr a * R /\ T = t /\ rets = [] /\
                 exists k'',
                   k' = k'' ++ k /\ k'' = f a_addr b_addr
            ).*)



(*Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R k t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string k t m (left::right::target::nil)%list
      (fun k' t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).*)
