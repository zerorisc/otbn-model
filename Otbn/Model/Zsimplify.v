Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.PushPullMod.
Local Open Scope Z_scope.

(* Helpful tactic for simplifying goals with `Z`. Performs only
   always-true and safe transformations so that it will not take a
   long time or make true goals false. *)
Ltac zsimplify_step :=
  lazymatch goal with
  | |- context [_ + 0] => rewrite Z.add_0_r
  | |- context [0 + _] => rewrite Z.add_0_l
  | |- context [0 - _] => rewrite Z.sub_0_l
  | |- context [_ - 0] => rewrite Z.sub_0_r
  | |- context [?x - ?x] => rewrite Z.sub_diag
  | |- context [_ * 0] => rewrite Z.mul_0_r
  | |- context [0 * _] => rewrite Z.mul_0_l
  | |- context [_ * 1] => rewrite Z.mul_1_r
  | |- context [1 * _] => rewrite Z.mul_1_l
  | |- context [0 ^ _] => rewrite Z.pow_0_l
  | |- context [_ ^ 0] => rewrite Z.pow_0_r
  | |- context [1 ^ _] => rewrite Z.pow_1_l
  | |- context [_ ^ 1] => rewrite Z.pow_1_r
  | |- context [0 mod _] => rewrite Zmod_0_l
  | |- context [_ mod 0] => rewrite Zmod_0_r
  | |- context [_ mod 1] => rewrite Z.mod_1_r
  | |- context [?x mod ?x] => rewrite Z_mod_same_full
  | |- context [Z.to_nat (Z.of_nat _)] => rewrite Nat2Z.id
  | |- context [Z.of_nat 0] => change (Z.of_nat 0) with 0
  | |- context [Z.of_nat 1] => change (Z.of_nat 1) with 1
  | _ => progress Z.push_pull_mod
  end.
Ltac zsimplify := repeat zsimplify_step.
