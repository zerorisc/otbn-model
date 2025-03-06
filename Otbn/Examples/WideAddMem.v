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
Require Import Otbn.Examples.WideAdd.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.Model.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Map.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.Zsimplify.
Require Import Otbn.Util.Tactics.SubstLets.
Import ListNotations.
Import Semantics.Coercions.
Local Open Scope Z_scope.

(*** Simple program that adds two 256-bit values from memory. ***)

(* Code reference:

     wide_add_mem:
       li       x2, 2
       li       x3, 3
       bn.lid   x2, 0(x12)
       bn.lid   x3, 0(x13)
       bn,add   w2, w2, w3
       bn.sid   x2, 0(x12)
       ret
 *)

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).
  
  Definition wide_add_mem_fn : otbn_function :=
    ("wide_add_mem",
      map.empty,
      [ (Addi x2 x0 2 : insn);
        (Addi x3 x0 3 : insn);
        (Bn_lid x2 false x12 false  0 : insn);
        (Bn_lid x3 false x13 false  0 : insn);
        (Bn_add w2 w2 w3 0 FG0 : insn);
        (Bn_sid x2 false x12 false  0 : insn);
        (Ret : insn)])%string.


  Lemma wide_add_mem_correct :
    forall regs wregs flags dmem cstack lstack (a b : word256) pa pb Ra Rb,
      is_word_aligned 32 pa = true ->
      is_word_aligned 32 pb = true ->
      word.unsigned pa + 32 < DMEM_BYTES ->
      word.unsigned pb + 32 < DMEM_BYTES ->
      map.get regs (gpreg x12) = Some pa ->
      map.get regs (gpreg x13) = Some pb ->
      (* note: the separation-logic setup does not require the operands to be disjoint *)
      (word_at pa a * Ra)%sep dmem ->
      (word_at pb b * Rb)%sep dmem ->
      returns
        (fetch:=fetch_ctx [wide_add_mem_fn])
        "wide_add_mem"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           (word_at pa (word.add a b) * Ra)%sep dmem'
           /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags'
           /\ clobbers [wdreg w2; wdreg w3] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x3] regs regs').
  Proof.
    cbv [wide_add_mem_fn returns]. intros; subst.
    
    repeat straightline_step.

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    ecancel_assumption.
  Qed.

End __.
