Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.PushPullMod.
Require Import Otbn.Lib.Bignum.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Util.Tactics.Zsimplify.
Import ListNotations.
Local Open Scope Z_scope.

Section Generic.
  Context {width} {word : word.word width} {word_ok : word.ok word}.

  Lemma eval_nil : eval (word:=word) [] = 0.
  Proof. reflexivity. Qed.

  Lemma eval_cons (x0 : word) x : eval (x0 :: x) = word.unsigned x0 + 2^width*(eval x).
  Proof. reflexivity. Qed.

  Lemma eval_app (x y : list word) n :
    Z.of_nat (length x) = n ->
    eval (x ++ y) = eval x + 2^(width*n) * (eval y).
  Proof.
    intros; subst. generalize dependent y.
    induction x; intros; [ rewrite !app_nil_l, Z.mul_0_r, eval_nil; lia | ].
    pose proof (word.width_pos (word:=word)).
    rewrite <-app_comm_cons, !eval_cons, IHx.
    cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_r.
    rewrite Z.pow_add_r; try lia.
  Qed.

  Lemma eval_bounds (x : list word) :
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
End Generic.

(* For separation-logic helpers, use specific 32/256 bit word sizes so
   there are fewer side conditions. *)
Section Specific.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}
    {word256 : word.word 256} {word256_ok : word.ok word256}
    {mem : map.map word32 byte} {mem_ok : map.ok mem}.

  Lemma split_bignum_nth n ptr (v : list word256) :
    (n < length v)%nat ->
    (32*Z.of_nat (length v) < 2^32) ->
    Lift1Prop.iff1 (bignum_at (mem:=mem) ptr v)
      (bignum_at ptr (List.firstn n v)
       * word_at (mem:=mem) (word.add ptr (word.of_Z (Z.of_nat n*32))) (nth n v (word.of_Z 0))
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

  Lemma split_bignum_expose_nth n ptr (v : list word256) :
    (n < length v)%nat ->
    (32*Z.of_nat (length v) < 2^32) ->
    Lift1Prop.iff1 (bignum_at ptr v)
      (Lift1Prop.ex1
         (fun v0 =>
            Lift1Prop.ex1
              (fun vn =>
                 Lift1Prop.ex1
                   (fun v1 =>
                      (emp (length v0 = n)
                       * emp (v = v0 ++ [vn] ++ v1)
                       * bignum_at ptr v0
                       * word_at (word.add ptr (word.of_Z (Z.of_nat n*32))) vn
                       * bignum_at (word.add ptr (word.of_Z (Z.of_nat (S n)*32))) v1)%sep)))).
  Proof.
    intros. rewrite (split_bignum_nth n) by lia.
    intro; split; intros.
    { exists (List.firstn n v), (nth n v (word.of_Z 0)), (List.skipn (S n) v).
      extract_ex1_and_emp_in_goal; ssplit; [ | | ].
      { ecancel_assumption. }
      { rewrite firstn_length; lia. }
      { symmetry; apply List.firstn_nth_skipn; lia. } }
    { extract_ex1_and_emp_in_hyps. subst.
      rewrite app_assoc, List.skipn_app_r by (rewrite app_length; cbn [length]; lia).
      rewrite <-app_assoc. cbn [List.app]. rewrite List.firstn_app_l by lia.
      rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
      ecancel_assumption. }
  Qed.
End Specific.
