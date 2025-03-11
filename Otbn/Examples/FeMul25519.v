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
          (* Partial products for multiply-reduce:
           *
           * | a0b0    | a0b1    | a0b2    | a0b3 |
           * |         | a1b0    | a1b1    | a1b2 |
           * |         |         | a2b0    | a2b1 |
           * |         |         |         | a3b0 |
           * |         |         |         |      |
           * | a1b3*38 | a2b3*38 | a3b3*38 |      |
           * | a2b2*38 | a3b2*38 |         |      |
           * | a3b1*38 |         |         |      |
           *
           * We can further optimize by computing the highest-weight partial products
           * as t = (a0b2 + a1b1 + a2b0 + a3b3*38 + (a0b3 + a1b2 + a2b1 + a3b0) << 64)
           * ahead of time and multiplying the upper half by 38 as well:
           *
           * | a0b0       | a0b1    | t0 | t1 |
           * |            | a1b0    |    |    |
           * |            |         |    |    |
           * |            |         |    |    |
           * |            |         |    |    |
           * | a1b3*38    | a2b3*38 |    |    |
           * | a2b2*38    | a3b2*38 |    |    |
           * | a3b1*38    | t3*38   |    |    |
           * | t2*38      |         |    |    |
           *)
          (* Precompute b3*38 at an offset of 128 and store in w18 (this step also
             clears the lower part of w18, which is important later).
               w18.U <= b3*38 *)
          bn.mulqacc.wo.z w18, w23.3, w30.0, 128, FG0;
          (* Accumulate partial products from the top two limbs first, and store the
             result in ACC and w21.U such that:
               ACC <= t2 + t3 << 64
               w18 <= t0 << 128 + t1 << 192 *)
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
               w18 <= (t0 << 128 + t1 << 192) mod p *)
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

Section Math.
  Local Infix "<<" := Z.shiftl (at level 40) : Z_scope.
  Local Infix ">>" := Z.shiftr (at level 40) : Z_scope.

  Definition p : Z := 2^255 - 19.

  Definition to_limb64 (x : Z) : Z * Z * Z * Z :=
    let x0 := x mod 2^64 in
    let x1 := (x >> 64) mod 2^64 in
    let x2 := (x >> 128) mod 2^64 in
    let x3 := (x >> 192) mod 2^64 in
    (x0, x1, x2, x3).

  (* TODO: derive this part *)
  Definition fe_mul_spec a b : Z :=
    let '(a0, a1, a2, a3) := to_limb64 a in
    let '(b0, b1, b2, b3) := to_limb64 b in
    let hi := mulqacc_spec 0 b3 38 128 in
    let acc := mulqacc_spec 0 a0 b2 0 in
    let acc := mulqacc_spec acc a0 b2 0 in
    let acc := mulqacc_spec acc a1 b1 0 in
    let acc := mulqacc_spec acc a3 (hi >> 64) 0 in
    let acc := mulqacc_spec acc a0 b3 64 in
    let acc := mulqacc_spec acc a1 b2 64 in
    let acc := mulqacc_spec acc a2 b1 64 in
    let acc := mulqacc_spec acc a3 b0 64 in
    let acc := mulqacc_spec acc a3 b0 64 in
    let hi := so_writeback_spec true hi acc in
    let acc := acc >> 128 in
    let hi := addm_spec hi 0 p in
    let acc := mulqacc_spec acc a1 b3 0 in
    let acc := mulqacc_spec acc a2 b2 0 in
    let acc := mulqacc_spec acc a3 b1 0 in
    let acc := mulqacc_spec acc a2 b3 64 in
    let acc := mulqacc_spec acc a3 b2 64 in
    let lo := acc in
    let acc := mulqacc_spec 0 lo 38 0 in
    let acc := mulqacc_spec acc lo 38 64 in
    let acc := mulqacc_spec acc lo 38 128 in
    let acc := mulqacc_spec acc lo 38 192 in
    let acc := mulqacc_spec acc a0 b0 0 in
    let acc := mulqacc_spec acc a0 b1 64 in
    let acc := mulqacc_spec acc a1 b0 64 in
    let lo := acc in
    let r := addm_spec lo hi p in
    r.

  (*
    let b3_38 := b3 * 38 in
    let t := a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3_38 in
    let t := t + ((a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) << 64) in
    let '(t0, t1, t2, t3) := to_limb64 t in
    let high := (t0 + t1 << 64) << 128 in
    let high := if (p <? high) then (high - p) else high in
    let low := a1 * b3 + a2 * b2 + a3 * b1 + t2 in
    let low := low + ((a2 * b3 + a3 * b2 + t3) << 64) in
    let low := low * 38 in
    let low := low + (a0 * b0 + ((a0 * b1 + a1 * b0) << 64)) in
    if (p <? low + high) then low + high - p else low + high.
   *)

  Lemma fe_mul_spec_correct a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    fe_mul_spec a b = (a * b) mod p.
  Admitted.
  
End Math.

Section Proofs.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).

  (*
  (* TODO: move *)
  Lemma addm_full_reduce x y m :
    word.unsigned x + word.unsigned y < 2 * m ->
    word.unsigned (addm_spec x y (word.of_Z m)) = (word.unsigned x + word.unsigned y) mod m.
  Admitted.
   *)

  Lemma fe_mul_correct regs wregs flags dmem cstack lstack a b :
    (* @param[in]  w22: a, first operand, a < 2^255 *)
    0 <= word.unsigned a < 2^255 ->
    map.get wregs (wdreg w22) = Some a ->
    (* @param[in]  w23: b, second operand, b < 2^255 *)
    0 <= word.unsigned b < 2^255 ->
    map.get wregs (wdreg w23) = Some b ->
    (* @param[in]  w30: constant, 38 *)
    map.get wregs (wdreg w30) = Some (word.of_Z 38) ->
    (* @param[in]  w31: all-zero *)
    map.get wregs (wdreg w31) = Some (word.of_Z 0) ->
    (* @param[in]  MOD: p, modulus = 2^255 - 19 *)
    map.get wregs (wsreg WSR_MOD) = Some (word.of_Z p) ->
    returns
      (fetch:=fetch_ctx [fe_mul])
      "fe_mul"%string regs wregs flags dmem cstack lstack
      (fun regs' wregs' flags' dmem' =>
         dmem = dmem'
         /\ (exists v,
                map.get wregs' (wdreg w22) = Some v
                /\ word.unsigned v = (word.unsigned a * word.unsigned b) mod p)
         (* clobbered registers: w18, w20 to w22 *)
         /\ clobbers [wdreg w18; wdreg w20; wdreg w21; wdreg w22; wsreg WSR_ACC] wregs wregs'
         /\ clobbers [] regs regs'
         (* clobbered flag groups: FG0 *)
         /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags').
  Proof.
    cbv [returns fe_mul]; intros; subst.
    repeat straightline_step.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    eexists; ssplit; [ eassumption | ].

    (* here we have to prove the math! *)
    etransitivity; [ | apply fe_mul_spec_correct; lia ].

    (* all the flags should be irrelevant, clear them to clean up the context *)
    lazymatch goal with
    | x := _ : bool |- _ => clear dependent x
    end.

    (* helpful assertion *)
    assert (p < 2^256) by (exact eq_refl).

    (* unfold fe_mul_spec and introduce all its lets *)
    cbv beta delta [fe_mul_spec].
    repeat lazymatch goal with
           | |- ?lhs = (match ?e with pair x y => ?f end) =>
               rewrite (surjective_pairing e); cbn iota;
               change (let x := fst e in let y := snd e in lhs = f); do 2 intro
           | |- ?lhs = (let x := ?e in ?f) =>
               change (let x := e in lhs = f); intro
           end.

    subst v37.
    lazymatch goal with
    | |- word.unsigned (addm_spec ?x ?y (word.of_Z ?m)) = (?a + ?b) mod ?m =>
        replace a with (word.unsigned x); [ replace b with (word.unsigned y) | ];
        [ apply addm_full_reduce | .. ]
    end.
    {
      apply addm_full_reduce.
    rewrite addm_full_reduce.
    rewrite word.unsigned_of_Z_nowrap by lia.
    Search addm_spec.
    
  Qed.


End Proofs.
