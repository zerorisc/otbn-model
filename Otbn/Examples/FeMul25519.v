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
Require Import coqutil.Z.bitblast.
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
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.

  Local Infix "<<" := Z.shiftl (at level 40) : Z_scope.
  Local Infix ">>" := Z.shiftr (at level 40) : Z_scope.

  Definition p : Z := 2^255 - 19.

  Lemma all_limbs_eq x :
    0 <= x < 2^256 ->
    x = (limb_spec x 0) + (limb_spec x 1) * 2^64 + (limb_spec x 2) * 2^128 + (limb_spec x 3) * 2^192.
  Proof.
    cbv [limb_spec]. intros. zsimplify.
    rewrite <-!Z.land_ones, <-!Z.shiftr_div_pow2, <-!Z.shiftl_mul_pow2 by lia.
    rewrite <-!Z.or_to_plus by (repeat (rewrite <-?Z.or_to_plus; try solve [Z.bitblast])).
    Z.bitblast.
    rewrite !Bool.andb_false_r. cbn [orb].
    apply Z.testbit_false; [ lia | ].
    rewrite Z.div_small; [ reflexivity | ].
    lazymatch goal with |- 0 <= x < 2^?n => assert (2^256 <= 2^n); [ | lia ] end.
    apply Z.pow_le_mono_r; lia.
  Qed.

  Section Formula.
    Context (a b : Z).

    Let a0 := limb_spec a 0.
    Let a1 := limb_spec a 1.
    Let a2 := limb_spec a 2.
    Let a3 := limb_spec a 3.
    Let b0 := limb_spec b 0.
    Let b1 := limb_spec b 1.
    Let b2 := limb_spec b 2.
    Let b3 := limb_spec b 3.
    
    (* high terms *)
    Definition t :=
      a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3 * 38
      + ((a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) << 64).

    Let t0 := limb_spec t 0.
    Let t1 := limb_spec t 1.
    Let t2 := limb_spec t 2.
    Let t3 := limb_spec t 3.

    Definition high := (t0 << 128) + (t1 << 192).
    Definition needs_mul38 :=
      t2 + (t3 << 64) + a1 * b3 + a2 * b2 + a3 * b1 
      + ((a2 * b3) << 64) + ((a3 * b2) << 64).
    Local Definition low :=
      needs_mul38 * 38 + a0 * b0 + ((a0 * b1) << 64) + ((a1 * b0) << 64).

    Definition fe_mul_formula := (low + high) mod p.

    Definition a_limbs := (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192).
    Lemma a_limbs_eq : 0 <= a < 2^256 -> a = a_limbs.
    Proof. apply all_limbs_eq. Qed.
    Definition b_limbs := (b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192).
    Lemma b_limbs_eq : 0 <= b < 2^256 -> b = b_limbs.
    Proof. apply all_limbs_eq. Qed.
    Definition t_limbs := (t0 + t1 * 2^64 + t2 * 2^128 + t3 * 2^192).
    Lemma t_limbs_eq : 0 <= t < 2^256 -> t = t_limbs.
    Proof. apply all_limbs_eq. Qed.

    Lemma t_formula_correct :
      0 <= a < 2^256 ->
      0 <= b < 2^256 ->
      (a * b) mod p = (a0 * b0 + (a0 * b1 + a1 * b0) * 2^64 + (a1 * b3 + a2 * b2 + a3 * b1) * 38 + (a2 * b3 + a3 * b2) * 2^64 * 38 + t * 2^128) mod p.
    Proof.
      intros. rewrite a_limbs_eq, b_limbs_eq by lia.
      cbv [a_limbs b_limbs t]. rewrite Z.shiftl_mul_pow2 by lia.
      Z.push_mod. change (38 mod p) with (2^256 mod p). Z.pull_mod.
      f_equal. lia.
    Qed.
    
    Lemma fe_mul_formula_correct :
      0 <= a < 2^256 ->
      0 <= b < 2^256 ->
      0 <= t < 2^256 ->
      fe_mul_formula = (a * b) mod p.
    Proof.
      intros. rewrite t_formula_correct by lia. rewrite t_limbs_eq by lia.
      cbv [fe_mul_formula low high needs_mul38 t_limbs].
      rewrite !Z.shiftl_mul_pow2 by lia.
      Z.push_mod. change (38 mod p) with (2^256 mod p). Z.pull_mod.
      f_equal. lia.
    Qed.

  End Formula.
  
  (* TODO: derive this part *)
  Definition fe_mul_spec a b : Z :=
    let a0 := word.wrap (limb_spec a 0) in
    let a1 := word.wrap (limb_spec a 1) in
    let a2 := word.wrap (limb_spec a 2) in
    let a3 := word.wrap (limb_spec a 3) in
    let b0 := word.wrap (limb_spec b 0) in
    let b1 := word.wrap (limb_spec b 1) in
    let b2 := word.wrap (limb_spec b 2) in
    let b3 := word.wrap (limb_spec b 3) in
    let hi := word.wrap (mulqacc_spec 0 b3 38 128) in
    let hi2 := word.wrap (limb_spec hi 2) in
    let hi3 := word.wrap (limb_spec hi 3) in
    let acc := word.wrap (mulqacc_spec 0 a0 b2 0) in
    let acc := word.wrap (mulqacc_spec acc a1 b1 0) in
    let acc := word.wrap (mulqacc_spec acc a2 b0 0) in
    let acc := word.wrap (mulqacc_spec acc a3 hi2 0) in
    let acc := word.wrap (mulqacc_spec acc a0 b3 64) in
    let acc := word.wrap (mulqacc_spec acc a1 b2 64) in
    let acc := word.wrap (mulqacc_spec acc a2 b1 64) in
    let acc := word.wrap (mulqacc_spec acc a3 b0 64) in
    let acc := word.wrap (mulqacc_spec acc a3 hi3 64) in
    let hi := word.wrap (so_writeback_spec true hi acc) in
    let acc := acc >> 128 in
    let hi := word.wrap (addm_spec hi 0 p) in
    let acc := word.wrap (mulqacc_spec acc a1 b3 0) in
    let acc := word.wrap (mulqacc_spec acc a2 b2 0) in
    let acc := word.wrap (mulqacc_spec acc a3 b1 0) in
    let acc := word.wrap (mulqacc_spec acc a2 b3 64) in
    let acc := word.wrap (mulqacc_spec acc a3 b2 64) in
    let lo := acc in
    let lo0 := word.wrap (limb_spec lo 0) in
    let lo1 := word.wrap (limb_spec lo 1) in
    let lo2 := word.wrap (limb_spec lo 2) in
    let lo3 := word.wrap (limb_spec lo 3) in
    let acc := word.wrap (mulqacc_spec 0 lo0 38 0) in
    let acc := word.wrap (mulqacc_spec acc lo1 38 64) in
    let acc := word.wrap (mulqacc_spec acc lo2 38 128) in
    let acc := word.wrap (mulqacc_spec acc lo3 38 192) in
    let acc := word.wrap (mulqacc_spec acc a0 b0 0) in
    let acc := word.wrap (mulqacc_spec acc a0 b1 64) in
    let acc := word.wrap (mulqacc_spec acc a1 b0 64) in
    let lo := acc in
    let r := word.wrap (addm_spec lo hi p) in
    r.

  Lemma limb_spec_bound v l : 0 <= limb_spec v l < 2^64.
  Proof. apply Z.mod_pos_bound. lia. Qed.

  Lemma limb3_spec_bound v n :
    0 <= v < 2^n -> 192 <= n -> 0 <= limb_spec v 3 < 2^(n - 192).
  Proof.
    intros. cbv [limb_spec].
    destr (256 <? n).
    { pose proof Z.pow_le_mono_r 2 64 (n-192) ltac:(lia) ltac:(lia).
      lazymatch goal with |- 0 <= ?x mod ?m < _ =>
                            pose proof Z.mod_pos_bound x m ltac:(lia) end.
      lia. }
    { pose proof Z.pow_le_mono_r 2 n 256 ltac:(lia) ltac:(lia).
      assert (v < 2 ^ (64 * 3) * 2 ^ 64) by (change (2^(64*3) * 2^64) with (2^256); lia).
      pose proof Z.div_lt_upper_bound v (2^(64 * 3)) (2^64) ltac:(lia) ltac:(lia).
      pose proof Z.div_pos v (2^(64*3)) ltac:(lia) ltac:(lia).
      rewrite Z.mod_small by lia.
      split; [ lia | ]. apply Z.div_lt_upper_bound; [ lia | ].
      rewrite <-Z.pow_add_r by lia. change (64 * 3) with 192.
      rewrite Zplus_minus. lia. }
  Qed.

  Lemma limb_spec_nowrap v l : word.wrap (limb_spec v l) = limb_spec v l.
  Proof. pose proof limb_spec_bound v l. apply Z.mod_small. lia. Qed.

  (* TODO: move *)
  Lemma addm_spec_bound x y m :
    0 <= x < 2^256 ->
    0 <= y < 2^256 ->
    0 <= m < 2^256 ->
    x + y < 2^256 + m ->
    0 <= addm_spec x y m < 2^256.
  Proof. cbv [addm_spec]. intros. destruct_one_match; lia. Qed.

  (* TODO: move *)
  Lemma addm_spec_full_reduce x y m :
    0 < m -> 0 <= x + y < 2 * m -> addm_spec x y m = (x + y) mod m.
  Proof.
    cbv [addm_spec]; intros. destruct_one_match; [ | rewrite Z.mod_small; lia ].
    rewrite Z.mod_eq by lia.
    pose proof Z.div_le_lower_bound (x + y) m 1 ltac:(lia) ltac:(lia).
    pose proof Z.div_lt_upper_bound (x + y) m 2 ltac:(lia) ltac:(lia).
    replace ((x + y) / m) with 1; lia.
  Qed.

  Lemma p_bound : 0 < p < 2^255.
  Proof. vm_compute; split; congruence. Qed.

  Ltac intro_limbs_with_bounds :=
    repeat
      lazymatch goal with
      | |- (let x := limb_spec ?y ?n in _) =>
          let v := fresh x in
          intro v;
          eassert (0 <= v < _) by (first [eapply (limb3_spec_bound y); [ eassumption | .. ]; lia
                                         | apply limb_spec_bound ])
      | |- 0 <= ?e /\ _ ?e _ =>
          lazymatch goal with
            |- ?G =>
              let P := (eval pattern e in G) in
              lazymatch P with
              | ?P _ =>
                  lazymatch e with                                
                  | (let x := limb_spec ?y ?n in ?f) =>
                      change (let x := limb_spec y n in P f); cbv beta
                  end
              end
          end
      end.

  Lemma t_bound_exact a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    0 <= t a b <= (2^64-1)*(2^64-1)*3 + (2^63-1)*(2^63-1)*38 + 2^64*((2^64-1)*(2^64-1)*2 + (2^64-1)*(2^63-1)*2).
  Proof.
    intros. cbv beta delta [t]. intro_limbs_with_bounds.
    change (255 - 192) with 63 in *.
    rewrite Z.shiftl_mul_pow2 by lia.
    split; [ lia |  nia ].
  Qed.

  Lemma t_bound a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    0 <= t a b < 2^194.
  Proof.
    split; [ | eapply Z.le_lt_trans ]; [ eapply t_bound_exact; lia .. | ].
    vm_compute. congruence.
  Qed.

  Lemma needs_mul38_bound a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    0 <= needs_mul38 a b < 2^194.
  Proof.
    intros; cbv beta delta [needs_mul38]. pose proof t_bound a b ltac:(lia) ltac:(lia).
    intro_limbs_with_bounds.
    rewrite !Z.shiftl_mul_pow2 by lia.
    split; [ lia | nia ].
  Qed.

  Lemma low_bound a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    0 <= low a b < p.
  Proof.
    intros; cbv beta delta [low]. pose proof t_bound a b ltac:(lia) ltac:(lia).
    intro_limbs_with_bounds.
    pose proof needs_mul38_bound a b ltac:(lia) ltac:(lia).
    rewrite !Z.shiftl_mul_pow2 by lia.
    split; [ lia | cbv [p]; nia ].
  Qed.
  
  Lemma high_bound a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    0 <= high a b < 2 * p.
  Proof.
    intros; cbv beta delta [high]. pose proof t_bound a b ltac:(lia) ltac:(lia).
    intro_limbs_with_bounds.
    rewrite !Z.shiftl_mul_pow2 by lia.
    split; [ lia | cbv [p]; nia ].
  Qed.

  Lemma b3_38_bound b :
    0 <= limb_spec b 3 * 38 < 2^128.
  Proof.
    pose proof limb_spec_bound b 3.
    lia.
  Qed.

  Lemma b3_38_limbs_eq b :
    0 <= b < 2^255 ->
    limb_spec b 3 * 38
    = ((limb_spec (limb_spec b 3 * 38 * 2 ^ 128) 3) * 2^64)
      + (limb_spec (limb_spec b 3 * 38 * 2 ^ 128) 2).
  Proof.
    cbv [limb_spec]. intros.
    change (2 ^ (64 * 2)) with (1 * 2^128).
    change (2 ^ (64 * 3)) with (2^64 * 2^128).
    rewrite !Z.div_mul_cancel_r by lia. zsimplify.
    change (2^64 * 2^128) with (2^192).
    assert (0 <= b / 2^192 < 2^64) by
      (split; [ apply Z.div_pos | apply Z.div_lt_upper_bound ]; lia).
    rewrite !(Z.mod_small (_ / _)) by
      (split; [ apply Z.div_pos | apply Z.div_lt_upper_bound ]; lia).
    rewrite Z.mod_eq by lia. lia.
  Qed.

  Lemma high_limbs_eq x :
    0 <= x < 2^256 ->
    x >> 128 = (limb_spec x 3) * 2^64 + (limb_spec x 2).
  Proof.
    cbv [limb_spec]. intros. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ (64 * 3)) with (2^128 * 2^64).
    change (2 ^ (64 * 2)) with (2^128).
    rewrite <-Z.div_div by lia.
    rewrite (Z.mod_small (_ / _ / _)) by
      (split; repeat first [ apply Z.div_pos | apply Z.div_lt_upper_bound | lia ]).
    rewrite Z.mod_eq by lia. lia.
  Qed.

  Lemma fe_mul_spec_equiv a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    fe_mul_spec a b = fe_mul_formula a b.
  Proof.
    pose proof p_bound.
    intros; cbv [fe_mul_formula]. cbv beta delta [fe_mul_spec].
    rewrite !limb_spec_nowrap.
    repeat lazymatch goal with
           | |- (let x := ?y in ?f) = ?g =>
               change (let x := y in (f = g)); intro
           end.
    
    pose proof t_bound a b ltac:(lia) ltac:(lia).

    (* Find the term that represents t and prove equivalence *)
    lazymatch goal with
    | x := context [so_writeback_spec _ _ ?vt] |- _ => assert (vt = t a b)
    end.
    { transitivity (t a b mod 2^256); [ | apply Z.mod_small; lia ].
      subst_lets. cbv [mulqacc_spec word.wrap t]. zsimplify.
      rewrite !Z.shiftl_mul_pow2 by lia.
      Z.push_pull_mod.
      assert (0 <= limb_spec b 3 * 38 * 2^128 < 2^256) by (pose proof b3_38_bound b; nia).
      rewrite (Z.mod_small (_ * 38 * _)) by lia.
      etransitivity; [ | rewrite <-(Z.mul_assoc _ (limb_spec b 3) 38);
                         rewrite b3_38_limbs_eq by lia; reflexivity ].
      f_equal; lia. }

    pose proof needs_mul38_bound a b ltac:(lia) ltac:(lia).
 
    (* Find the term that represents needs_mul38 * 38 and prove equivalence *)
    lazymatch goal with
    | x := context [mulqacc_spec _ ?v 38 192] |- _ =>
             assert (x = needs_mul38 a b * 38)
    end.
    { transitivity ((needs_mul38 a b * 38) mod 2^256); [ | apply Z.mod_small; lia ].
      (* substitute only the *38 terms *)
      repeat match goal with
             | x := word.wrap (mulqacc_spec ?acc ?v 38 ?s) |- _ =>
                      lazymatch goal with |- context [x] => idtac end;
                      change_in_goal x (word.wrap (mulqacc_spec acc v 38 s))
             | x := word.wrap (limb_spec ?v ?n) |- _ =>
                      lazymatch goal with |- context [x] => idtac end;
                      change_in_goal x (word.wrap (limb_spec v n))
             end.
      rewrite !limb_spec_nowrap.
      (* find the needs_mul38 subterm *)
      lazymatch goal with |- context [limb_spec ?v _] => replace v with (needs_mul38 a b) end.
      2:{ symmetry.
          transitivity (needs_mul38 a b mod 2^256); [ | apply Z.mod_small; lia ].
          (* substitute all lets, but use equality for t *)
          repeat lazymatch goal with
                 | H : ?x = t a b |- context [?x] => rewrite H
                 | _ => subst_lets_step
                 end.
          cbv [mulqacc_spec word.wrap needs_mul38]. zsimplify.
          rewrite !Z.shiftl_mul_pow2 by lia.
          Z.push_pull_mod. rewrite high_limbs_eq by lia.
          f_equal; lia. }
      
      subst_lets. cbv [mulqacc_spec word.wrap t]. zsimplify.
      rewrite !Z.shiftl_mul_pow2 by lia.
      Z.push_pull_mod.
      etransitivity; [ | rewrite (all_limbs_eq (needs_mul38 a b)) by lia; reflexivity ].
      f_equal; lia. }
    
    subst_lets_step.
    lazymatch goal with
    | |- word.wrap (addm_spec ?x ?y p) = (low a b + high a b) mod p =>
        pose proof low_bound a b ltac:(lia) ltac:(lia);
        pose proof high_bound a b ltac:(lia) ltac:(lia);
        replace x with (low a b);
        [ replace y with (addm_spec (high a b) 0 p) | ];
        [ pose proof Z.mod_pos_bound (high a b) p ltac:(lia);
          pose proof Z.mod_pos_bound (low a b + high a b) p ltac:(lia);
          rewrite (addm_spec_full_reduce (high a b)), Z.add_0_r by lia;
          rewrite addm_spec_full_reduce, Z.add_mod_idemp_r by lia;
          apply Z.mod_small; lia
        | symmetry; try subst y
        | symmetry; try subst x ]
    end.
    { (* prove high part equivalence *)
      lazymatch goal with
      | |- word.wrap (addm_spec ?x 0 p) = addm_spec (high a b) 0 p =>
          replace x with (high a b);
          [ apply Z.mod_small; apply addm_spec_bound; lia | symmetry; try subst x ]
      end.
      cbv [so_writeback_spec high].
      lazymatch goal with
      | H : ?x = t a b |- context [?x] => rewrite H
      end.
      lazymatch goal with
      | |- context [Z.land ?x (Z.ones 128)] =>
          replace (Z.land x (Z.ones 128)) with 0
      end.
      { zsimplify. cbv [word.wrap limb_spec].
        rewrite !Z.shiftl_mul_pow2 by lia. zsimplify.
        change (2^256) with (2^128*2^128). rewrite Z.mul_mod_distr_r by lia.
        rewrite (Z.rem_mul_r _ (2^64) (2^64)) by lia.
        lia. }
      { pose proof b3_38_bound b. subst_lets.
        rewrite Z.land_ones by lia. cbv [word.wrap mulqacc_spec].
        rewrite !Z.shiftl_mul_pow2 by lia.
        rewrite (Z.mod_small _ (2^256)) by lia.
        zsimplify. Z.push_mod. rewrite Z.mod_same by lia.
        zsimplify. lia. } }

    transitivity ((low a b) mod 2^256); [ | apply Z.mod_small; lia ].
    cbv [low].
    repeat lazymatch goal with
           | H : ?x = t a b |- context [?x] => rewrite H
           | H : ?x = needs_mul38 a b * 38 |- context [?x] => rewrite H
           | _ => subst_lets_step
           end.
    cbv [mulqacc_spec word.wrap]. zsimplify.
    rewrite !Z.shiftl_mul_pow2 by lia.
    Z.push_pull_mod. f_equal; lia.
  Qed.
    

  Lemma fe_mul_spec_correct a b :
    0 <= a < 2^255 ->
    0 <= b < 2^255 ->
    fe_mul_spec a b = (a * b) mod p.
  Proof.
    intros. pose proof t_bound a b ltac:(lia) ltac:(lia).
    rewrite fe_mul_spec_equiv by lia.
    apply fe_mul_formula_correct; lia.
  Qed.
  
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

  Lemma limb0_small_constant x : 0 <= x < 2^64 -> limb_spec x 0 = x.
  Proof. intros; cbv [limb_spec]. zsimplify. apply Z.mod_small; lia. Qed.


  Ltac crush_step :=
    lazymatch goal with
    | |- word.unsigned (word.of_Z ?x) = word.wrap ?y =>
        replace y with x; [ solve [apply word.unsigned_of_Z] | ]
    | |- limb_spec _ ?n = limb_spec _ ?n => f_equal
    | |- addm_spec _ _ _ = addm_spec _ _ _ => f_equal
    | |- mulqacc_spec _ _ _ _ = mulqacc_spec _ _ _ _ => f_equal
    | |- so_writeback_spec _ _ _ = so_writeback_spec _ _ _ => f_equal
    | |- word.unsigned (word.sru ?x (word.of_Z ?n)) = Z.shiftr ?y ?n =>
        rewrite word.unsigned_sru_nowrap by (rewrite (word.unsigned_of_Z_nowrap n); lia);
        rewrite (word.unsigned_of_Z_nowrap n) by lia; f_equal
    | |- word.unsigned (word.of_Z ?x) = ?x => apply word.unsigned_of_Z_nowrap; lia
    | |- word.unsigned (word.of_Z (limb_spec (word.unsigned (word.of_Z 38)) 0)) = 38 =>
        rewrite (word.unsigned_of_Z_nowrap 38) by lia;
        rewrite (limb0_small_constant 38), (word.unsigned_of_Z_nowrap 38) by lia
    | |- ?x = ?x => reflexivity
    end.
  Ltac subst_next_step :=
    match goal with
    | x := ?y |- _ =>
             lazymatch goal with
             | |- word.unsigned x = ?rhs => change (word.unsigned y = rhs)
             | |- ?lhs = x => change (lhs = y)
             end
    end.
  Ltac subst_next := subst_next_step; repeat subst_next_step.
  Ltac crush := try subst_next; repeat progress (repeat crush_step; subst_next).

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
    assert (0 <= p < 2^256) by (vm_compute; split; congruence).

    (* unfold fe_mul_spec and introduce all its lets *)
    cbv beta delta [fe_mul_spec].
    repeat lazymatch goal with
           | |- ?lhs = (match ?e with pair x y => ?f end) =>
               rewrite (surjective_pairing e); cbn iota;
               change (let x := fst e in let y := snd e in lhs = f);
               let x := fresh in let y := fresh in
               intros x y; subst x y
           | |- ?lhs = (let x := ?e in ?f) =>
               change (let x := e in lhs = f); intro
           end.

    crush.    
  Qed.

End Proofs.
