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
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Tactics.Mapsimpl.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.SubstLets.
Import ListNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(*** Large code-generation process to test scaling. ***)

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).

  (* Test scaling with a large codegen. *)
  Definition repeat_add (n : nat) : otbn_function :=
    (("add" ++ String.of_nat n)%string,
      map.empty,
      (Addi x2 x0 0 : insn) :: repeat (Add x2 x2 x3 : insn) n ++ [(Ret : insn)]).
  Definition add100_fn : otbn_function := Eval vm_compute in (repeat_add 100).

  (* helper lemma *)
  Lemma mul_by_add_step x (a : word32) n :
    0 < n ->
    x = word.mul a (word.of_Z (n - 1)) ->
    word.add x a = word.mul a (word.of_Z n).
  Proof.
    intros; subst. cbv [Z.sub].
    rewrite word.ring_morph_add, word.ring_morph_opp.
    ring.
  Qed.

  Lemma add100_correct :
    forall regs wregs flags dmem cstack lstack a,
      map.get regs (gpreg x3) = Some a ->
      returns
        (fetch:=fetch_ctx [add100_fn])
        "add100"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x2) = Some (word.mul a (word.of_Z 100))
           /\ dmem' = dmem
           /\ clobbers [] wregs wregs'
           /\ clobbers [gpreg x2] regs regs').
  Proof.
    cbv [returns]; intros.
    straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step. (* .57s *)

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers ..].
    mapsimpl. apply (f_equal Some).
    repeat (apply mul_by_add_step; [ lia | ];
            cbn [Z.sub Z.add Z.opp Z.pos_sub Pos.pred_double]).
    lazymatch goal with |- ?x = word.mul _ (word.of_Z 0) => subst x end.
    cbv [addi_spec]. destruct_one_match; try lia; [ ].
    ring.
    Time Qed. (* 0.75s *)
End __.
