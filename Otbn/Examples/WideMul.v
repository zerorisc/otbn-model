Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import Otbn.Examples.WideAdd.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Tactics.Mapsimpl.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.Zsimplify.
Require Import Otbn.Util.Tactics.SubstLets.
Import ListNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(*** Build 32x256-bit multiplication out of loops and wide addition. ***)

Section Defs.
  Import ISA.Notations.
  
  Definition wide_mul_fn : otbn_function :=
    ltac:(make_function
         "wide_mul"%string
         ([ "" -: bn.xor w2, w2, w2, FG0
            ; ""-: beq x4, x0, "_wide_mul_end"
            ; "" -: loop x4
            ; "" -: jal x1, "wide_add"
            ; "" -: loopend (bn.addi w2, w5, 0, FG0)
            ; "_wide_mul_end" -: ret
           ]%otbn)%string).
End Defs.

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).


  Lemma wide_mul_correct :
    forall regs wregs flags dmem cstack lstack (a v : word256) (b: word32),
      map.get wregs (wdreg w2) = Some v -> (* ignored, xored *)
      map.get wregs (wdreg w3) = Some a ->
      map.get regs (gpreg x4) = Some b ->
      (length cstack < 8)%nat ->
      (length lstack < 8)%nat ->
      returns
        (fetch:=fetch_ctx [wide_mul_fn; wide_add_fn])
        "wide_mul"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w2) = Some (word.mul a (word.of_Z (word.unsigned b)))
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [wide_mul_fn returns]. intros; subst.
    repeat straightline_step.

    (* branch; use branch helper lemma *)
    eapply eventually_beq.
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { simplify_side_condition; reflexivity. }
    { (* case: b = 0, exit early *)
      intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
      rewrite word.unsigned_of_Z_0. rewrite word.mul_0_r.
      ssplit; try reflexivity; [ | solve_clobbers .. ].
      mapsimpl; subst_lets.
      rewrite word_xor_same. reflexivity. }
    (* case: b <> 0, proceed *)
    intros; subst.

    pose proof (word.unsigned_range b).
    assert (0 < word.unsigned b).
    { lazymatch goal with H : b <> word.of_Z 0 |- _ =>
                            apply word.unsigned_inj' in H end.
      rewrite word.unsigned_of_Z_0 in *.
      lia. }
 
    (* loop; use loop invariant lemma *)
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w2) = Some (word.mul a (word.sub (word.of_Z (word.unsigned b)) (word.of_Z (Z.of_nat i))))
           /\ map.get wregs' (wdreg w3) = Some a
           /\ map.get regs' (gpreg x4) = Some b
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; simplify_side_condition; zsimplify; try reflexivity; [ | solve_clobbers .. ].
      subst_lets. apply f_equal. rewrite word_xor_same, Z2Nat.id by lia.
      ring. }
    { (* invariant step; proceed through loop and prove invariant still holds *)
      intros; subst. repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.

      (* helper assertion that mul and add don't share symbols *)
      assert (function_symbols_disjoint wide_add_fn wide_mul_fn).
      { cbv [function_symbols_disjoint]; cbn [wide_add_fn wide_mul_fn fst snd].
        ssplit; mapsimpl; try congruence; [ ].
        cbv [map.disjoint]; intros *. rewrite map.get_empty; congruence. }

      (* jump to "bignum_add" function *)
      eapply eventually_jump.
      { reflexivity. }
      { lia. }
      { apply wide_add_correct; eauto. }
      { intros.
        rewrite fetch_ctx_cons_ne; [ eassumption | ].
        eapply fetch_fn_disjoint; eauto; [ ].
        eapply fetch_ctx_singleton_iff; eauto. }

      (* post-jump; continue *)
      cbv beta. intros; subst.
      repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             end.
      track_registers_combine.

      repeat straightline_step.      

      (* end of loop; use loop-end helper lemma *)
      eapply eventually_loop_end; [ reflexivity .. | ].
      simplify_side_condition; track_registers_update.
      destruct_one_match.
      { (* case: i = 0, loop ends *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; mapsimpl; [ ].
        simplify_side_condition; subst_lets; zsimplify.
        apply f_equal. ring. }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; mapsimpl; [ ].
        simplify_side_condition. subst_lets; zsimplify.
        apply f_equal.
        replace (word.of_Z (width:=256) (Z.of_nat (S (S i))))
          with (word.add (width:=256) (word.of_Z (Z.of_nat (S i))) (word.of_Z 1));
          [ ring | ].
        apply word.unsigned_inj.
        rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
        cbv [word.wrap]. rewrite Z.mod_small by lia. lia. } }
 
    (* invariant implies postcondition (i.e. post-loop code) *)
    zsimplify. rewrite word.sub_0_r. intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           end.
    simplify_side_condition.
    repeat straightline_step.
    intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; eauto.
  Qed.
End __.
