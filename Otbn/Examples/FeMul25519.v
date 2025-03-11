Require Import Coq.Init.Byte.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Z.PushPullMod.
Require Import coqutil.Z.ZLib.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Lib.Bignum.
Require Import Otbn.Lib.BignumProperties.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.Mapsimpl.
Require Import Otbn.Util.Tactics.SubstLets.
Require Import Otbn.Util.Tactics.Zsimplify.
Import ListNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(* Field multiplication modulo 2^255-19. *)

Section Defs.
  Import ISA.Notations.

  (** Original function specification:
   *
   * Multiply two field elements and reduce modulo p.
   *
   * Returns c = (a * b) mod p.
   *
   * The inputs a and b must be at most 2^255 bits, although it is not necessary
   * for them to be fully reduced modulo p. This routine runs in constant time.
   *
   * Flags: Flags have no meaning beyond the scope of this subroutine.
   *
   * @param[in]  w22: a, first operand, a < 2^255
   * @param[in]  w23: b, second operand, b < 2^255
   * @param[in]  w30: constant, 38
   * @param[in]  w31: all-zero
   * @param[in]  MOD: p, modulus = 2^255 - 19
   * @param[out] w22: c, result
   *
   * clobbered registers: w18, w20 to w22
   * clobbered flag groups: FG0
   *)
  Definition fe_mul : otbn_function :=
    ("fe_mul"%string,
      map.empty,
      [[
          (* Precompute b3*38 at an offset of 128 and store in w18 (this step also
             clears the lower part of w18, which is important later).
               w18.U <= b3*38 *)
          bn.mulqacc.wo.z w18, w23.3, w30.0, 128, FG0;
          (* Accumulate partial products from the top two limbs first, and store the
             result in ACC and w21.U such that:
               ACC <= t2 + t3 << 64
               w21 <= t0 << 128 + t1 << 192 *)
          bn.mulqacc.z          w22.0, w23.2, 0; (* a0b2 *)
          bn.mulqacc            w22.1, w23.1, 0; (* a1b1 *)
          bn.mulqacc            w22.2, w23.0, 0; (* a2b0 *)
          bn.mulqacc            w22.3, w18.2, 0; (* a3*((b3*38)[63:0]) *)
          bn.mulqacc            w22.0, w23.3, 64; (* a0b3 *)
          bn.mulqacc            w22.1, w23.2, 64; (* a1b2 *)
          bn.mulqacc            w22.2, w23.1, 64; (* a2b1 *)
          bn.mulqacc            w22.3, w23.0, 64; (* a3b0 *)
          bn.mulqacc.so  w18.U, w22.3, w18.3, 64, FG0; (* a3*((b3*38) >> 64) *)
          (* Reduce the high part modulo p. This guarantees a full reduction because
             the written-back value is at most (2^128 - 1) * 2^128 < 2 * p.
               w18 <= (t0 + t1 << 64) mod p *)
          bn.addm    w18, w18, w31;
          (* Accumulate partial products that need to be multiplied by 38 and are
             fully within the first 256 bits of the result. Result max. 194 bits.
               w20 <= (a1b3 + a2b2 + a3b1 + t2) + (a2b3 + a3b2 + t3) << 64 *)
          bn.mulqacc            w22.1, w23.3, 0;  (* a1b3 *)
          bn.mulqacc            w22.2, w23.2, 0;  (* a2b2 *)
          bn.mulqacc            w22.3, w23.1, 0;  (* a3b1 *)
          bn.mulqacc            w22.2, w23.3, 64; (* a2b3 *)
          bn.mulqacc.wo    w20, w22.3, w23.2, 64, FG0; (* a3b2 *)
          (* Multiply the accumulator by 38, storing the result in the accumulator.
             This value is at most 200 bits and so will not overflow the accumulator.
                  ACC <= w20*38 *)
          bn.mulqacc.z          w20.0, w30.0, 0;
          bn.mulqacc            w20.1, w30.0, 64;
          bn.mulqacc            w20.2, w30.0, 128;
          bn.mulqacc            w20.3, w30.0, 192;
          (* Continue accumulating partial products for the lower half of the
             product.
               w20 <= (a0b0 + a1b3*38 + a2b2*38 + a3b1*38 + t2*38)
                      + (a0b1 + a1b0 + a2b3*38 + a3b2*38 + t3*38) << 64  *)
          bn.mulqacc            w22.0, w23.0, 0;   (* a0b0 *)
          bn.mulqacc            w22.0, w23.1, 64;  (* a0b1 *)
          bn.mulqacc.wo    w20, w22.1, w23.0, 64, FG0; (* a1b0 *)
          (* Add the high and low parts of the product.
               w22 <= (a * b) mod p *)
          bn.addm    w22, w20, w18;
          ret ]]%otbn).

End Defs.
