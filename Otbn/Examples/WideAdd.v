Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.Model.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Map.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Import ListNotations.
Import Semantics.Coercions.
Local Open Scope Z_scope.

(*** Very simple program that adds two 256-bit registers. ***)

(* Code reference:

     wide_add:
       bn.add w5, w2, w3
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
 
  Definition wide_add_fn : otbn_function :=
    ("wide_add"%string,
      map.empty,
      [(Bn_add w5 w2 w3 0 FG0: insn);
       (Ret : insn)]).

  
  Lemma wide_add_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get wregs (wdreg w2) = Some a ->
      map.get wregs (wdreg w3) = Some b ->
      returns
        (fetch:=fetch_ctx [wide_add_fn])
        "wide_add"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w5) = Some (word.add a b)
           /\ map.get flags' (flagC FG0) = Some (2^256 <=? word.unsigned a + word.unsigned b)
           /\ dmem' = dmem
           /\ clobbers [flagC FG0; flagM FG0; flagZ FG0; flagL FG0] flags flags'
           /\ clobbers [wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [wide_add_fn returns]. intros; subst.
    straightline_step.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ mapsimpl | mapsimpl | solve_clobbers .. ].
  Qed.

End __.
