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
Require Import Otbn.Model.Clobbers.
Require Import Otbn.Model.ISA.
Require Import Otbn.Model.Linker.
Require Import Otbn.Model.Map.
Require Import Otbn.Model.Semantics.
Require Import Otbn.Model.SemanticsProperties.
Require Import Otbn.Model.StraightlineStep.
Require Import Otbn.Model.SubstLets.
Import ListNotations.
Import Semantics.Coercions.
Local Open Scope Z_scope.

(*** The world's most basic OTBN test program: adds two 32-bit registers. ***)

(* Code reference:

     start:
       addi x2, x0, 2
       addi x3, x0, 3
       jal  x1, add
       sw   x5, 0(x0)
       ecall

     add:
       add  x5, x2, x3
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

  Definition add_fn : otbn_function :=
    ("add"%string,
      map.empty,
      [(Add x5 x2 x3 : insn);
       (Ret : insn)]).
  Definition start_fn : otbn_function :=
    ("start",
      map.empty,
      [ (Addi x2 x0 2 : insn);
        (Addi x3 x0 3 : insn);
        (Jal x1 "add" : insn);
        (Sw x0 x5 0 : insn) ;
        (Ecall : insn)])%string.

  Lemma add_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      returns
        (fetch:=fetch_ctx [add_fn])
        "add"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x5) = Some (word.add a b)
           /\ dmem' = dmem
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
           /\ clobbers [gpreg x5] regs regs').
  Proof.
    cbv [add_fn returns]. intros; subst.
    repeat straightline_step.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    mapsimpl.
  Qed.

  (*** Test proving the *linked* version of the program. ***)

  (* NOTE: this is not a normal use-case! I just wanted to see if it would work. *)

  Definition add_prog : program := ltac:(link_program [start_fn; add_fn]).

  Lemma add_prog_correct v dmem R :
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

    (* TODO: The `eventually_jump` lemma can't handle different fetch functions here. *)
    eapply eventually_step_cps.
    simplify_side_condition.
 
    repeat straightline_step.

    (* TODO: since we handled `jal` manually, we have to handle `ret` manually too. *)
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

End __.
