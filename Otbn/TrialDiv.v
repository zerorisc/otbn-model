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
Require Import Otbn.Model.
Import ListNotations.
Import Otbn.Model.Coercions.
Local Open Scope Z_scope.

(* Test out the model by trying to prove the fold_bignum function for RSA trial division. *)

(***
Original code:

/**
 * Partially reduce a value modulo m such that 2^32 mod m == 1.
 *
 * Returns r such that r mod m = x mod m and r < 2^35.
 *
 * Can be used to speed up modular reduction on certain numbers, such as 3, 5,
 * 17, and 65537.
 *
 * Because we know 2^32 mod m is 1, it follows that in general 2^(32*k) for any
 * k are all 1 modulo m. This includes 2^256, so when we receive the input as
 * a bignum in 256-bit limbs, we can simply all the limbs together to get an
 * equivalent number modulo m:
 *  x = x[0] + 2^256 * x[1] + 2^512 * x[2] + ...
 *  x \equiv x[0] + x[1] + x[2] + ... (mod F4)
 *
 * From there, we can essentially use the same trick to bisect the number into
 * 128-bit, 64-bit, and 32-bit chunks and add these together to get an
 * equivalent number modulo m. This operation is visually sort of like folding
 * the number over itself repeatedly, which is where the function gets its
 * name.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dptr_x, pointer to first limb of x in dmem
 * @param[in]  x30: plen, number of 256-bit limbs for x
 * @param[in]  w24: constant, 2^256 - 1
 * @param[in]  w31: all-zero
 * @param[out] w23: r, result
 *
 * clobbered registers: x2, w22, w23
 * clobbered flag groups: FG0
 */
fold_bignum:
  /* Initialize constants for loop. */
  li      x22, 22

  /* Copy input pointer. */
  addi    x2, x16, 0

  /* Initialize sum to zero and clear FG0.C.
       w23 <= 0
       FG0.C <= 0 */
  bn.addi  w23, w31, 0

  /* Iterate through the limbs of x and add them together.

     Loop invariants for iteration i (i=0..n-1):
       x2 = dptr_x + i*32
       x22 = 22
       (w23 + FG0.C) \equiv x[0] + x[1] + ... + x[i-1] (mod m)
   */
  loop    x30, 2
    /* Load the next limb.
         w22 <= x[i] */

    bn.lid   x22, 0(x2++)

    /* Accumulate the new limb, incorporating the carry bit from the previous
       round if there was one (this works because 2^256 \equiv 1 mod m).
         w23 <= (w23 + x[i] + FG0.C) mod 2^256
         FG0.C <= (w23 + x[i] + FG0.C) / 2^256 */
    bn.addc  w23, w23, w22

  /* Isolate the lower 128 bits of the sum.
       w22 <= w23[127:0] */
  bn.and   w22, w23, w24 >> 128

  /* Add the two 128-bit halves of the sum, plus the carry from the last round
     of the sum computation. The sum is now up to 129 bits.
       w23 <= (w22 + (w23 >> 128) + FG0.C) */
  bn.addc  w23, w22, w23 >> 128

  /* Isolate the lower 64 bits of the sum.
       w22 <= w23[63:0] */
  bn.and   w22, w23, w24 >> 192

  /* Add the two halves of the sum (technically 64 and 65 bits). A carry was
     not possible in the previous addition since the value is too small. The
     value is now up to 66 bits.
       w23 <= (w22 + (w23 >> 64)) */
  bn.add   w23, w22, w23 >> 64

  /* Isolate the lower 32 bits of the sum.
       w22 <= w23[31:0] */
  bn.and   w22, w23, w24 >> 224

  /* Add the two halves of the sum (technically 32 and 34 bits). A carry was
     not possible in the previous addition since the value is too small.
       w23 <= (w22 + (w23 >> 32)) */
  bn.add   w23, w22, w23 >> 32

  ret

 ***)

(* generic bignums *)
Section WithWord.
  Context {width} {word : word.word width} {word_ok : word.ok word}.

  Definition eval (x : list word) : Z :=
    fold_right (fun xi acc => word.unsigned xi + 2^width*acc) 0 x.

  Lemma eval_nil : eval [] = 0.
  Proof. reflexivity. Qed.

  Lemma eval_cons x0 x : eval (x0 :: x) = word.unsigned x0 + 2^width*(eval x).
  Proof. reflexivity. Qed.

  Lemma eval_app x y n :
    Z.of_nat (length x) = n ->
    eval (x ++ y) = eval x + 2^(width*n) * (eval y).
  Proof.
    intros; subst. generalize dependent y.
    induction x; intros; [ rewrite !app_nil_l, Z.mul_0_r, eval_nil; lia | ].
    pose proof word.width_pos.
    rewrite <-app_comm_cons, !eval_cons, IHx.
    cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_r.
    rewrite Z.pow_add_r; lia.
  Qed.

  Lemma eval_bounds x :
    0 <= eval x < 2^(width*Z.of_nat (length x)).
  Proof.
    induction x as [|x0 ?]; intros; cbn [length]; [ rewrite eval_nil; lia | ].
    pose proof word.unsigned_range x0. pose proof word.width_pos.
    rewrite eval_cons. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
    nia.
  Qed.

  Lemma le_split_eval n (x : list word) :
    (n = Z.to_nat (width / 8) * length x)%nat ->
    width mod 8 = 0 ->
    le_split n (eval x) = concat (map (fun w => le_split
                                                  (Z.to_nat (width / 8)) (word.unsigned w)) x).
  Proof.
    intros; subst; induction x; cbn [map length concat];
      [ rewrite Nat.mul_0_r; reflexivity | ].
    rewrite eval_cons, <-IHx.
    apply nth_error_ext; intro n.
    destr (n <? Z.to_nat (width / 8))%nat.
    { rewrite nth_error_app1 by (rewrite length_le_split; lia).
      rewrite !nth_error_le_split by lia.
      apply (f_equal Some). apply byte.unsigned_inj.
      rewrite !byte.unsigned_of_Z. cbv [byte.wrap].
      Z.bitblast. rewrite ?Bool.andb_true_l.
      pose proof Z.div_mod width 8 ltac:(lia).
      rewrite <-(Z.mod_pow2_bits_low (_ + _) width) by lia.
      Z.push_mod. zsimplify. rewrite Z.mod_pow2_bits_low by lia.
      reflexivity. }
    { rewrite nth_error_app2 by (rewrite length_le_split; lia).
      rewrite !length_le_split.
      (* handle out-of-bounds index case *)
      destr (n <? Z.to_nat (width / 8) * S (length x))%nat;
        [ | repeat 
              lazymatch goal with
              | |- context [@nth_error ?A ?n ?l] =>
                  replace (@nth_error A n l) with (@None A)
                  by (symmetry; apply nth_error_None;
                      rewrite length_le_split; lia)
              end; reflexivity ].
      rewrite !nth_error_le_split by lia.
      apply (f_equal Some). apply byte.unsigned_inj.
      rewrite !byte.unsigned_of_Z. cbv [byte.wrap].
      Z.bitblast. rewrite ?Bool.andb_true_l.
      pose proof Z.div_mod width 8 ltac:(lia).
      lazymatch goal with |- Z.testbit (?a + 2^width * ?b) ?i = Z.testbit ?b ?j =>
                            replace i with (j+width) by lia; rewrite (Z.mul_comm (2^width) b)
      end.
      rewrite <-Z.div_pow2_bits, Z.div_add by lia.
      rewrite Z.div_small by apply word.unsigned_range.
      zsimplify; reflexivity. }
  Qed.

End WithWord.

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).

  Definition fold_bignum : otbn_function :=
    ("fold_bignum"%string,
      map.empty,
      [(Addi x22 x0 22 : insn);
       (Addi x2 x16 0 : insn);
       (Bn_addi w23 w31 0 FG0 : insn);
       (Loop x30 : insn);
       (Bn_lid x22 false x2 true 0 : insn);
       (Bn_addc w23 w23 w22 0 FG0 : insn);
       (LoopEnd : insn);
       (Bn_and w22 w23 w24 (-128) FG0 : insn);
       (Bn_addc w23 w22 w23 (-128) FG0 : insn);
       (Bn_and w22 w23 w24 (-192) FG0 : insn);
       (Bn_add w23 w22 w23 (-64) FG0 : insn);
       (Bn_and w22 w23 w24 (-224) FG0 : insn);
       (Bn_add w23 w22 w23 (-32) FG0 : insn);
       (Ret : insn)]).

  Definition fold_bignum_array (x : list word256) : Z :=
    fold_left (fun acc x => (acc mod 2^256 + x + acc / 2^256)) (map word.unsigned x) 0.

  Definition fold_bignum_spec (x : list word256) : Z :=
    let x := fold_bignum_array x in
    let x := x mod 2^128 + (x / 2^128) mod 2^128 + x / 2^256 in
    let x := x mod 2^64 + x / 2^64 in
    let x := x mod 2^32 + x / 2^32 in
    x.

  Lemma fold_bignum_step x y m :
    y mod m = 1 -> 0 < m -> 0 < y ->
    (x mod y + x / y) mod m = x mod m.
  Proof.
    intros. rewrite (Z.mod_eq x y) by lia.
    Z.push_mod. replace (y mod m) with 1 by lia.
    rewrite Z.mul_1_l. Z.push_pull_mod.
    f_equal; lia.
  Qed.

  Lemma fold_left_add_init a x : fold_left Z.add x a = a + fold_left Z.add x 0.
  Proof.
    generalize dependent a. induction x; intros; [ cbn [fold_left]; lia | ].
    cbn [fold_left]. rewrite !IHx with (a:=_ + _).
    lia.
  Qed.

  Lemma fold_bignum_array_correct m (x : list word256) :
    2^256 mod m = 1 -> 0 < m ->
    (fold_left Z.add (map word.unsigned x) 0) mod m = (eval x) mod m.
  Proof.
    intros; induction x; intros; [ reflexivity | ].
    cbn [map fold_left]. rewrite Z.add_0_l, eval_cons.
    rewrite fold_left_add_init. Z.push_mod.
    rewrite IHx. replace (2^256 mod m) with 1 by lia.
    rewrite Z.mul_1_l. Z.push_pull_mod. f_equal; lia.
  Qed.

  Definition bignum_at (ptr : word32) (v : list word256) : mem -> Prop :=
    bytes_at ptr (le_split (Z.to_nat 32 * length v) (eval v)).

  
  Lemma split_bignum_nth n ptr v :
    (n < length v)%nat ->
    (32*Z.of_nat (length v) < 2^32) ->
    Lift1Prop.iff1 (bignum_at ptr v)
      (bignum_at ptr (List.firstn n v)
       * word_at (word.add ptr (word.of_Z (Z.of_nat n*32))) (nth n v (word.of_Z 0))
       * bignum_at (word.add ptr (word.of_Z (Z.of_nat (S n)*32))) (List.skipn (S n) v))%sep.
  Proof.
    intros; cbv [bignum_at].
    rewrite !le_split_eval by reflexivity.
    rewrite <-(List.firstn_nth_skipn _ n v (word.of_Z 0)) at 1 by lia.
    change (256 / 8) with 32.
    do 2 (rewrite map_app, concat_app, map.of_list_word_at_app;
          rewrite sep_eq_putmany by
            (apply map.adjacent_arrays_disjoint;
             erewrite !List.length_concat_same_length
               by (apply List.Forall_map, Forall_forall; intros; apply length_le_split);
             rewrite !map_length, ?app_length, ?firstn_length, ?skipn_length by lia;
             cbn [length]; lia)).
    cbn [List.app map concat]. rewrite app_nil_r.
    erewrite !List.length_concat_same_length
      by (apply List.Forall_map, Forall_forall; intros; apply length_le_split).
    rewrite ?map_length, ?length_le_split.
    rewrite ?firstn_length, ?Nat.min_l by lia.
    cbv [word_at]. change (256 / 8) with 32.
    rewrite Nat2Z.inj_mul, Z2Nat.id in * by lia.
    rewrite Nat2Z.inj_succ, Z.mul_succ_l.
    rewrite word.ring_morph_add, word.add_assoc.
    cancel.
  Qed.

  (* helper lemma for shift expressions *)
  Lemma and_shift_right_ones (x : word256) n :
    0 <= n < 256 ->
    word.unsigned (word.and x (word.sru (word.of_Z (2^256 - 1)) (word.of_Z n))) = word.unsigned x mod 2^(256 - n).
  Proof.
    intros. rewrite word.unsigned_and.
    rewrite word.unsigned_sru_shamtZ by lia.
    rewrite word.unsigned_of_Z_nowrap by lia.
    change (2^256-1) with (Z.ones 256).
    rewrite Z.shiftr_div_pow2, Z.ones_div_pow2 by lia.
    rewrite Z.land_ones by lia.
    apply Z.mod_small.
    pose proof Z.mod_pos_bound (word.unsigned x) (2^(256-n)) ltac:(lia).
    assert (2^(256-n) <= 2^256) by (apply Z.pow_le_mono; lia).
    lia.
  Qed.

  (* helper lemma for shift expressions *)
  Lemma shift_right_ones (x : word256) n :
    word.unsigned (word.sru x (word.of_Z n)) = word.unsigned x / 2^n.
  Admitted.

  (* helper lemma for stepwise equivalence *)
  Lemma fold_bignum_step_word (x : word256) y n :
    0 < n < 256 ->
    word.unsigned x = y ->
    word.unsigned
      (word.add (word.and x (word.sru (word.of_Z (2 ^ 256 - 1)) (word.of_Z (256 - n))))
         (word.sru x (word.of_Z n))) = y mod 2 ^ n + y / 2 ^ n.
  Proof.
    intros; subst. rewrite word.unsigned_add.
    rewrite and_shift_right_ones, shift_right_ones.    
    pose proof word.unsigned_range x.
    pose proof Z.mod_pos_bound (word.unsigned x) (2^n) ltac:(lia).
    pose proof Z.div_lt_upper_bound
      (word.unsigned x) (2^n) (2^(256-n))
      ltac:(lia) ltac:(rewrite <-Z.pow_add_r by lia; replace (n + (256 - n)) with 256; lia).
    pose proof Z.div_pos (word.unsigned x) (2^n) ltac:(lia) ltac:(lia).
    replace (256 - (256 - n)) with n by lia.
    assert (2^n + 2^(256 - n) < 2^256); [ | apply Z.mod_small; lia ].
    destr (n =? 1); [ lia | ].
    change (2^256) with (2^255 + 2^255).
    assert (2^(256 - n) < 2^255) by (apply Z.pow_lt_mono_r; lia).
    assert (2^n <= 2^255) by (apply Z.pow_le_mono; lia).
    lia.
  Qed.

  (* helper lemma for expressions with carries *)
  Lemma addc_high_bit (x : word256) (y : Z):
    (word.unsigned x + 2 ^ 256 * y) / 2 ^ 256 = y.
  Proof.
    rewrite Z.add_comm, Z.mul_comm.
    rewrite Z.div_add_l by lia. rewrite Z.div_small; [ lia | ].
    apply word.unsigned_range.
  Qed.

  (* helper lemma that makes it easier to prove the folding steps *)
  Lemma pow2_mod1_multiple w i m :
    0 <= w ->
    0 <= i ->
    1 < m ->
    2^w mod m = 1 ->
    2^(w*i) mod m = 1.
  Proof.
    intros. generalize dependent w. generalize dependent i.
    (* natlike induction on i *)
    lazymatch goal with
    | |- forall i, 0 <= i -> ?P =>
        apply (natlike_ind (fun i => P))
    end.
    { intros. rewrite Z.mul_0_r, Z.pow_0_r, Z.mod_1_l by lia. lia. }
    { intros. rewrite Z.mul_succ_r, Z.pow_add_r by lia. Z.push_mod.
      repeat match goal with H : context [2^_ mod m = 1] |- _ => rewrite H by lia end.
      rewrite Z.mul_1_r, Z.mod_1_l by lia; lia. }
  Qed.

  (* TODO: move *)
  Lemma carry_bit_add_div x y :
    0 <= x < 2^256 ->
    0 <= y < 2^256 ->
    Z.b2z (carry_bit (x + y)) = (x + y) / 2^256.
  Admitted.

  (* TODO: move *)
  Lemma carry_bit_addc_div x y c :
    0 <= x < 2^256 ->
    0 <= y < 2^256 ->
    Z.b2z (carry_bit (x + y + Z.b2z c)) = (x + y + Z.b2z c) / 2^256.
  Admitted.

  Lemma fold_bignum_correct :
    forall regs wregs flags dmem cstack lstack
           (dptr_x plen : word32) x m R,
      (length lstack < 8)%nat ->
      is_word_aligned 32 dptr_x = true ->
      word.unsigned dptr_x + 32 * word.unsigned plen < DMEM_BYTES ->
      map.get regs (gpreg x16) = Some dptr_x ->
      map.get regs (gpreg x30) = Some plen ->
      map.get wregs (wdreg w24) = Some (word.of_Z (2^256 - 1)) ->
      map.get wregs (wdreg w31) = Some (word.of_Z 0) ->
      0 <= eval x <= 2^(256*word.unsigned plen) ->
      (2^32 mod m = 1) ->
      1 < m ->
      word.unsigned plen = Z.of_nat (length x) ->
      (length x <> 0)%nat ->
      (bignum_at dptr_x x * R)%sep dmem ->
      returns
        (fetch:=fetch_ctx [fold_bignum])
        "fold_bignum"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>           
           dmem = dmem'
           /\ (exists v,
                  map.get wregs' (wdreg w23) = Some v
                  /\ word.unsigned v = fold_bignum_spec x)
           /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags'
           /\ clobbers [wdreg w22; wdreg w23] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x22] regs regs').
  Proof.    
    cbv [fold_bignum returns]. intros; subst.
    track_registers_init.

    (* helpful assertions *)
    assert (2^256 mod m = 1) by (apply (pow2_mod1_multiple 32 8); lia).
    assert (2^128 mod m = 1) by (apply (pow2_mod1_multiple 32 4); lia).
    assert (2^64 mod m = 1) by (apply (pow2_mod1_multiple 32 2); lia).

    straightline_step.
    straightline_step.
    straightline_step.

    (*
     Loop invariants (at end of loop) for iteration i (i=n..1):
       x2 = dptr_x + (n-i+1)*32
       x22 = 22
       (w23 + FG0.C) \equiv x[0] + x[1] + ... + x[n-i] (mod m)
     *)
    let regs := lazymatch goal with
                  |- eventually run1 _ (otbn_busy  _ ?regs ?wregs ?flags ?dmem _ _) =>
                    regs end in
    let wregs := lazymatch goal with
                  |- eventually run1 _ (otbn_busy  _ ?regs ?wregs ?flags ?dmem _ _) =>
                    wregs end in
    let flags := lazymatch goal with
                  |- eventually run1 _ (otbn_busy  _ ?regs ?wregs ?flags ?dmem _ _) =>
                    flags end in
    let dmem := lazymatch goal with
                  |- eventually run1 _ (otbn_busy  _ ?regs ?wregs ?flags ?dmem _ _) =>
                    dmem end in
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x2) = Some (word.add dptr_x
                                              (word.of_Z (32*(Z.of_nat (length x - i)))))
           /\ map.get regs' (gpreg x22) = Some (addi_spec (word.of_Z 0) 22)
           /\ (exists acc c,
                  map.get wregs' (wdreg w23) = Some acc
                  /\ map.get flags' (flagC FG0) = Some c
                  /\ word.unsigned acc + 2^256 * Z.b2z c
                     = fold_bignum_array (List.firstn (length x - i) x))
           /\ dmem' = dmem
           /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags'
           /\ clobbers [wdreg w22; wdreg w23] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x22] regs regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; simplify_side_condition; zsimplify; try reflexivity.
      all:try replace (Z.to_nat (word.unsigned plen)) with (length x) by lia.
      all:rewrite ?Nat.sub_diag.
      all:try solve [apply map.only_differ_same].
      { (* memory pointer *)
        subst_lets. apply f_equal.
        cbv [addi_spec]. destruct_one_match; try lia; [ ].
        apply f_equal. apply f_equal. ring. }
      { (* accumulator equation *)
        cbn [fold_left List.firstn]. subst_lets.
        rewrite word.unsigned_of_Z_0.
        reflexivity. } }
    { (* invariant step; proceed through loop and prove invariant still holds *)
      intros.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | _ => progress subst
             end.

      (* assert that the pointer is in bounds of DMEM *)
      lazymatch goal with
      | H : map.get ?regs (gpreg _) = Some (word.add dptr_x ?offset) |- context [?regs] =>
          assert (word.unsigned (word.add dptr_x offset) + 32 < DMEM_BYTES)
      end.
      { rewrite word.unsigned_add.
        pose proof word.unsigned_range dptr_x.
        assert (DMEM_BYTES < 2^32) by (vm_compute; congruence).
        rewrite word.unsigned_of_Z_nowrap by lia.
        cbv [word.wrap]; rewrite Z.mod_small by lia. lia. }

      (* rewrite the seplogic statement to expose the word we're going to load *)
      lazymatch goal with
      | H : sep (bignum_at _ _) _ ?m |- context[?m] =>
          seprewrite_in (split_bignum_nth (length x - S i)) H; [ lia .. | ]
      end.
      extract_ex1_and_emp_in_hyps.
      subst.

      straightline_step.
      straightline_step.
      
      (* end of loop; use loop-end helper lemma *)
      eapply eventually_loop_end; [ reflexivity .. | ].
      (* prove that the remaining length of the bignum matches the remaining iterations *)
      lazymatch goal with
      | H : (?i < Z.to_nat (word.unsigned plen))%nat |- context[?x ++ [?y] ++ ?z] =>
          assert (i = length z)%nat
          by (rewrite ?app_length in *; cbn [length] in *; destruct x, z; cbn [length] in *;
              lia)
      end.
      destruct_one_match.
      { (* case: i = 0, loop ends *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ | ].
        { simplify_side_condition; subst_lets; zsimplify.
          apply (f_equal Some). apply word.unsigned_inj.
          rewrite !word.unsigned_add, !word.unsigned_of_Z.
          cbv [word.wrap]. Z.push_pull_mod. f_equal. lia. }
        {
          (* at this point the remainder of the bignum is nil *)
          lazymatch goal with
          | |- context[?x ++ [?y] ++ ?z] =>
              destruct z;
              [ rewrite !app_nil_r in *
              | rewrite ?app_length in *; cbn [length] in *; lia ]
          end.
          rewrite Nat.sub_0_r. cbv [fold_bignum_array] in *.
          rewrite List.firstn_all. rewrite map_app. cbn [map].
          rewrite fold_left_app. cbn [fold_left].
          repeat lazymatch goal with
                 | H : context [List.firstn (length (?a ++ [?b]) - 1) (_ ++ [_])] |- _ =>
                     rewrite List.firstn_app_l in H by (rewrite ?app_length; cbn [length]; lia)
                 end.
          do 2 eexists; subst_lets; ssplit; try reflexivity; [ ].
          rewrite !word.unsigned_add, !word.unsigned_of_Z by lia.
          cbv [word.wrap]. Z.push_mod.
          lazymatch goal with H : _ = fold_left ?f ?x ?a0
                              |- context [fold_left ?f ?x ?a0] => rewrite <-H end.
          Z.push_mod. rewrite Z.mod_same, Z.mul_0_l, Z.mod_0_l, Z.add_0_r by lia.
          rewrite carry_bit_addc_div by (eauto using word.unsigned_range).
          Z.push_pull_mod.
          rewrite (Z.mod_eq (_ + _ + _) (2^256)) by lia.
          rewrite addc_high_bit.
          rewrite (Z.mod_small (word.unsigned _)) by apply word.unsigned_range.
          lia. } }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        lazymatch goal with
        | H : (?i < Z.to_nat (word.unsigned plen))%nat |- context[?x ++ [?y] ++ ?z] =>
            assert (i = length z)%nat
            by (rewrite ?app_length in *; cbn [length] in *; destruct x, z; cbn [length] in *;
                lia)
        end.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ | ].
        { simplify_side_condition; subst_lets; zsimplify.
          apply (f_equal Some). apply word.unsigned_inj.
          rewrite !word.unsigned_add, !word.unsigned_of_Z.
          cbv [word.wrap]. Z.push_pull_mod. f_equal. lia. }
        { do 2 eexists. ssplit; eauto; [ ]. subst_lets.
          lazymatch goal with
          | H : context [List.firstn (length (?a ++ [?b] ++ ?c) - _) (?a ++ [?b] ++ ?c)]
            |- _ =>
              rewrite List.firstn_app_l in H by (rewrite ?app_length; cbn [length]; lia)
          end.
          rewrite app_assoc.
          rewrite List.firstn_app_l by (rewrite ?app_length; cbn [length]; lia).
          cbv [fold_bignum_array] in *. rewrite map_app, fold_left_app; cbn [map fold_left].
          rewrite carry_bit_addc_div by (eauto using word.unsigned_range).
          rewrite !word.unsigned_add, !word.unsigned_of_Z by lia.
          cbv [word.wrap]. Z.push_pull_mod.
          lazymatch goal with H : _ = fold_left ?f ?x ?a0
                              |- context [fold_left ?f ?x ?a0] => rewrite <-H end.
          rewrite (Z.mod_eq (_ + _ + _)) by lia.
          Z.push_mod. zsimplify. Z.pull_mod.
          rewrite addc_high_bit.
          rewrite (Z.mod_small (word.unsigned _)) by apply word.unsigned_range.
          lia. } } }

    
    (* invariant implies postcondition (i.e. post-loop code) *)
    rewrite Nat.sub_0_r, List.firstn_all. intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           | _ => progress subst
           end.
    simplify_side_condition.

    track_registers_combine.

    straightline_step.
    straightline_step.
    straightline_step.
    straightline_step.
    straightline_step.
    straightline_step.
    
    intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; eauto; [ ].
    eexists; ssplit; eauto; [ ].
    (* prove the equality one let at a time *)
    cbv beta delta [fold_bignum_spec].
    repeat lazymatch goal with
           | |- ?lhs = (let x := ?y in ?e) =>
               change (let x := y in lhs = e); intro
           end.
    repeat lazymatch goal with
           | |- word.unsigned _ = ?z mod 2^?n + ?z / 2^?n =>
               apply (fold_bignum_step_word _ _ n); [ lia | ]
           | |- word.unsigned ?v = ?x => progress subst x
           end.

    (* first fold is different from the others because it has a carry *)
    subst_lets.
    rewrite !word.unsigned_add.
    rewrite and_shift_right_ones, shift_right_ones.
    lazymatch goal with |- context [Z.b2z ?c] =>
                          assert (0 <= Z.b2z c < 2) by (destruct c; cbn; lia) end.
    rewrite word.unsigned_of_Z_nowrap by lia.
    change (256 - 128) with 128.
    lazymatch goal with H : _ = fold_bignum_array _ |- _ => rewrite <-H end.
    cbv [word.wrap]. Z.push_mod. change (2^256 mod 2^128) with 0.
    zsimplify. rewrite (Z.mod_small (Z.b2z _)) by lia.
    lazymatch goal with |- context [(?x mod (2^128)) mod 2^256] =>
                          pose proof Z.mod_pos_bound x (2^128) ltac:(lia);
                          rewrite (Z.mod_small (x mod 2^128) (2^256)) by lia
    end.
    lazymatch goal with |- context [(word.unsigned ?x / (2^128)) mod 2^256] =>
                          pose proof word.unsigned_range x;
                          pose proof Z.div_pos (word.unsigned x) (2^128) ltac:(lia) ltac:(lia);
                          pose proof Z.div_lt_upper_bound (word.unsigned x) (2^128) (2^128) ltac:(lia) ltac:(lia);
                          rewrite (Z.mod_small (word.unsigned x / 2^128) (2^256)) by lia
    end.
    rewrite (Z.mod_small (_ + _ / 2^128)) by lia.
    rewrite addc_high_bit.
    lazymatch goal with |- context [(?a + 2^256 * ?b) / 2^128] =>
                          replace (a + 2^256 * b) with ((2^128*b)*2^128 + a) by lia;
                          rewrite Z.div_add_l by lia
    end.
    rewrite (Z.mod_small _ (2^256)) by lia.
    Z.push_mod. rewrite Z.mod_same by lia. zsimplify.
    rewrite (Z.mod_small (_ / 2^128)) by lia.
    lia.
  Qed.
  Print Assumptions fold_bignum_correct.
