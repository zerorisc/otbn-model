Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import Otbn.Examples.Add32.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Linker.Properties.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.SubstLets.
Import ListNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(*** Test proving the *linked* version of a simple program. ***)

(* NOTE: this is not a normal use-case! I just wanted to see if it would work. *)

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).

  (* First, just try to prove the post-link program correct without
     reusing any function specs or the linker proofs. *)
  Lemma add_prog_correct_raw v dmem R :
    (word32_at (word.of_Z 0) v * R)%sep dmem ->
    eventually
      (run1 (fetch:=fetch add_prog))
      (fun st =>
         match st with
         | otbn_done _ dmem =>
             (word32_at (word.of_Z 0) (word.of_Z 5) * R)%sep dmem
         | _ => False
         end)
      (start_state dmem).
  Proof.
    cbv [add_prog start_state]; intros.
    assert (word.unsigned (word:=word32) (word.of_Z 0) + 4 < DMEM_BYTES)
      by (cbv [DMEM_BYTES]; rewrite word.unsigned_of_Z_0; lia).
    repeat straightline_step.
    eapply eventually_step_cps.
    simplify_side_condition. 
    repeat straightline_step.
    eapply eventually_step_cps.
    simplify_side_condition.
    repeat straightline_step.
    eapply eventually_ecall; [ reflexivity | ].
    use_sep_assumption.
    lazymatch goal with
      |- Lift1Prop.iff1 (word_at ?ptr ?v1 * _)%sep (word_at ?ptr ?v2 * _)%sep =>
        replace v2 with v1; [ ecancel | ]
    end.
    subst_lets.
    cbv [addi_spec]. repeat destruct_one_match; try lia; [ ].
    apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
    cbv [word.wrap]. Z.push_pull_mod. reflexivity.
  Qed.

  (* Prove the pre-linked version of the program, using the function specification. *)
  Lemma add_prog_correct_prelink regs wregs flags dmem (v : word32) R :
    (word_at (word.of_Z 0) v * R)%sep dmem ->
    exits
      (fetch:=fetch_ctx [start_fn; add_fn])
      "start"%string regs wregs flags dmem [] []
      (word_at (width:=32) (word.of_Z 0) (word.of_Z 5) * R)%sep
      (fun errs => False).
  Proof.
    cbv [exits start_fn start_state]; intros.
    assert (word.unsigned (word:=word32) (word.of_Z 0) + 4 < DMEM_BYTES)
      by (cbv [DMEM_BYTES]; rewrite word.unsigned_of_Z_0; lia).

    repeat straightline_step.

    eapply eventually_jump;
      [ reflexivity | cbn [length]; lia | eapply add_correct; solve [eauto] | | ].
    { intros.
      rewrite fetch_ctx_cons_ne; [ eassumption | ].
      eapply fetch_fn_disjoint; eauto; [ eapply fetch_ctx_singleton_iff; eauto | ].
      cbv; intuition congruence. }

    (* simplify hyps and combine register tracking post-jump *)
    cbv beta. intros; subst.
    repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    track_registers_combine.

    repeat straightline_step.

    eapply eventually_ecall; ssplit; [ reflexivity .. | ].
    use_sep_assumption.
    lazymatch goal with
      |- Lift1Prop.iff1 (word_at ?ptr ?v1 * _)%sep (word_at ?ptr ?v2 * _)%sep =>
        replace v2 with v1; [ ecancel | ]
    end.
    subst_lets. cbv [addi_spec]. repeat destruct_one_match; try lia; [ ].
    apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
    cbv [word.wrap]. Z.push_pull_mod. reflexivity.
  Qed.

  (* Use the linker proofs and the pre-link proof to prove the post-link program *)
  Lemma add_prog_correct_postlink dmem (v : word32) R :
    (word_at (word.of_Z 0) v * R)%sep dmem ->
    exits
      (fetch:=fetch add_prog)
      0%nat map.empty map.empty map.empty dmem [] []
      (word_at (width:=32) (word.of_Z 0) (word.of_Z 5) * R)%sep
      (fun errs => False).
  Proof.
    set (fns:=[start_fn; add_fn]). intros.
    assert (link fns = inl add_prog) by reflexivity.
    let x := eval vm_compute in (link_symbols [start_fn; add_fn]) in
      match x with
      | inl ?x =>
          pose (syms:=x)
      | _ => fail
      end.
    assert (link_symbols fns = inl syms) by reflexivity.
    assert (find_global_offset fns "start"%string = Some 0%nat) by reflexivity.
    eapply link_exits; eauto using add_prog_correct_prelink.
  Qed.
End __.
