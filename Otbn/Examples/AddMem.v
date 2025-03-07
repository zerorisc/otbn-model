Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Map.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Import ListNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(*** A simple function that adds two 32-bit values from memory. ***)

Section Defs.
  Import ISA.Notations.

  Definition add_mem_fn : otbn_function :=
    ("add_mem"%string,
      map.empty,
      [ lw   x2, 0(x12)
        ; lw   x3, 0(x13)
        ; add  x5, x2, x3
        ; sw   x5, 0(x12)
        ; ret]%otbn).
End Defs.

Section Proofs.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).
  
  Lemma add_mem_correct :
    forall regs wregs flags dmem cstack lstack a b pa pb Ra Rb,
      is_word_aligned 4 pa = true ->
      is_word_aligned 4 pb = true ->
      word.unsigned pa + 4 < DMEM_BYTES ->
      word.unsigned pb + 4 < DMEM_BYTES ->
      map.get regs (gpreg x12) = Some pa ->
      map.get regs (gpreg x13) = Some pb ->
      (* note: the separation-logic setup does not require the operands to be disjoint *)
      (word32_at pa a * Ra)%sep dmem ->
      (word32_at pb b * Rb)%sep dmem ->
      returns
        (fetch:=fetch_ctx [add_mem_fn])
        "add_mem"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           (word32_at pa (word.add a b) * Ra)%sep dmem'
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x3; gpreg x5] regs regs').
  Proof.
    cbv [add_mem_fn returns]. intros; subst.

    repeat straightline_step.

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    ecancel_assumption.
  Qed.

End Proofs.
