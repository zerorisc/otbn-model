Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Util.Map.
Require Import Otbn.Util.Tactics.Mapsimpl.
Require Import Otbn.Util.Tactics.SubstLets.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Local Open Scope Z_scope.

(*** Helpful tactics for proving programs correct. ***)

(*
Usage tl;dr:
- Use `repeat straightline_step` to process straightline instructions.
- Use `print_next_insn` to see which instruction will be fetched next in your program.
  - If control instruction, then apply a lemma from SemanticsProperties (e.g. `eventually_beq`).
  - If straightline instruction, then `straightline_step` failed to prove side conditions.
- The `find_loop_end` tactic is useful for applying loop invariant lemmas; see Examples/.
*)

Ltac solve_is_word_aligned_step t :=
  lazymatch goal with
  | H : is_word_aligned ?sz ?a = true |- is_word_aligned ?sz ?a = true => exact H
  | |- is_word_aligned _ (word.of_Z 0) = true => apply is_word_aligned_0; t
  | |- is_word_aligned 4 4 = true =>
      apply is_word32_aligned_imm; apply Z.mod_same; t
  | |- is_word_aligned 32 32 = true =>
      apply is_word256_aligned_imm; apply Z.mod_same; t
  | |- is_word_aligned 4 (word.of_Z (_ * 4)) = true =>
      apply is_word32_aligned_imm; apply Z.mod_mul; t
  | |- is_word_aligned 32 (word.of_Z (_ * 32)) = true =>
      apply is_word256_aligned_imm; apply Z.mod_mul; t
  | |- is_word_aligned ?sz (word.of_Z (?sz * ?x)) = true =>
      rewrite (Z.mul_comm sz x)
  | |- is_word_aligned 4 (word.of_Z _) = true => apply is_word32_aligned_imm; t
  | |- is_word_aligned 32 (word.of_Z _) = true => apply is_word256_aligned_imm; t
  | |- is_word_aligned 4 (word.add ?a ?offset) = true =>
      apply is_word32_aligned_add
  | |- is_word_aligned 32 (word.add ?a ?offset) = true =>
      apply is_word256_aligned_add
  | |- is_word_aligned _ ?x = true =>
      (subst x || fail "cannot determine if" x "is word-aligned")
  | _ => t
  end.

Ltac solve_is_word_aligned := repeat solve_is_word_aligned_step ltac:(lia).

Ltac solve_word_at :=
  match goal with
  | H : sep (word_at ?p _) _ ?m |- sep (word_at ?p _) _ ?m => eapply H
  | _ => use_sep_assumption; ecancel
  end.

Ltac simplify_side_condition_step :=
  match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- context [word.add ?a (word.of_Z 0)] => rewrite (word.add_0_r a)
  | |- context [?x =? ?x] => rewrite (Z.eqb_refl x)
  | |- context [?x <? ?x] => rewrite (Z.ltb_irrefl x)
  | |- context [(0 <? S ?x)%nat] => destr (0 <? S x)%nat; [ | lia ]
  | |- context [word.unsigned (addi_spec (word.of_Z 0) ?imm)] =>
      rewrite (li_spec imm) by lia
  | |- context [if is_valid_lui_imm ?v then _ else _] =>
      replace (is_valid_lui_imm v) with true by (cbv [is_valid_lui_imm]; lia)
  | |- context [if is_valid_shamt ?v then _ else _] =>
      replace (is_valid_shamt v) with true by (cbv [is_valid_shamt]; lia)
  | |- context [if is_valid_arith32_imm ?v then _ else _] =>
      replace (is_valid_arith32_imm v) with true by (cbv [is_valid_arith32_imm]; lia)
  | |- context [if is_valid_arith256_imm ?v then _ else _] =>
      replace (is_valid_arith256_imm v) with true by (cbv [is_valid_arith256_imm]; lia)
  | |- context [if is_valid_rshi_imm ?v then _ else _] =>
      replace (is_valid_arith256_imm v) with true by (cbv [is_valid_rshi_imm]; lia)
  | |- context [if is_valid_mem_offset ?v then _ else _] =>
      replace (is_valid_mem_offset v) with true by (cbv [is_valid_mem_offset]; cbn; lia)
  | |- context [if is_valid_wide_mem_offset ?v then _ else _] =>
      replace (is_valid_wide_mem_offset v) with true by (cbv [is_valid_wide_mem_offset]; cbn; lia)
  | |- context [if is_valid_arith256_shift_imm ?s then _ else _] =>
      replace (is_valid_arith256_shift_imm s) with true by (vm_compute; lia)
  | |- context [if is_valid_mulqacc_shift ?s then _ else _] =>
      replace (is_valid_mulqacc_shift s) with true by (vm_compute; lia)
  | |- assert_or_error _ (is_word_aligned ?width ?a) _ _ =>
      replace (is_word_aligned width a) with true by (symmetry; solve_is_word_aligned)
  | |- assert_or_error _ (?x <? DMEM_BYTES) _ _ =>
      destr (x <? DMEM_BYTES); [ | lia ]
  | |- assert_or_error _ (is_valid_wdr_index ?i) _ _ =>
      replace (is_valid_wdr_index i) with true
      by (cbv [is_valid_wdr_index]; subst_lets; rewrite ?li_spec by lia; reflexivity)
  | |- context [(_ + 0)%nat] => rewrite Nat.add_0_r
  | |- context [fetch_fn (?s, _, _) (?s, _)] => rewrite fetch_fn_name by auto
  | |- match fetch_fn ?fn ?pc with _ => _ end = Some _ => reflexivity
  | |- context [fetch_fn _ _] =>
      erewrite fetch_fn_sym by
      (cbn [fst snd]; first [ congruence | mapsimpl ])
  | H : sep (ptsto ?addr _) _ ?m |- map.get ?m ?addr = Some _ =>
      eapply get_sep; solve [apply H]
  | |- map.get _ _ = Some _ => mapsimpl
  | H : map.get ?m ?k = Some _ |- context [match map.get ?m ?k with _ => _ end] =>
      rewrite H
  | |- context [match map.get _ _ with _ => _ end] => mapsimpl
  | |- context [advance_pc (?dst, ?off)] =>
      change (advance_pc (dst, off)) with (dst, S off)
  | |- apply_shift _ 0 _ => eapply apply_shift_0
  | |- apply_shift _ (Zneg ?p) _ => change (Zneg p) with (Z.opp (Zpos p))
  | |- apply_shift _ (- _) _ => eapply apply_shiftr; [ lia | cbn; congruence | ]
  | |- apply_shift _ _ _ => eapply apply_shiftl; [ lia | cbn; congruence | ]
  | |- @store_word _ _ _ 32 _ _ _ _ _ =>
      eapply store_word32_step; [ solve_is_word_aligned | lia | solve_word_at | ]
  | |- @load_word _ _ _ _ 32 _ _ _ _ =>
      eapply load_word32_step; [ solve_is_word_aligned | lia | solve_word_at | ]
  | |- @store_word _ _ _ 256 _ _ _ _ _ =>
      eapply store_word256_step; [ solve_is_word_aligned | lia | solve_word_at | ]
  | |- @load_word _ _ _ _ 256 _ _ _ _ =>
      eapply load_word256_step; [ solve_is_word_aligned | lia | solve_word_at | ]
  | |- read_wdr_indirect ?v _ _ =>
      eapply read_wdr_indirect_step; eexists; split;
      [ subst_lets; rewrite ?li_spec by lia; cbn [lookup_wdr]; reflexivity | ]
  | |- write_wdr_indirect ?v _ _ _ =>
      eapply write_wdr_indirect_step; eexists; split; 
      [ subst_lets; rewrite ?li_spec by lia; cbn [lookup_wdr]; reflexivity | ]
  | |- (_ < _) => lia
  | |- (_ <= _) => lia                                   
  | |- (_ < _)%nat => lia
  | |- (_ <= _)%nat => lia
  | |- Some _ = Some _ => reflexivity
  | _ => first [ progress
                   cbn [run1 strt1 read_gpr write_gpr ctrl1
                          read_gpr_from_state read_gpr_inc increment_gprs
                          read_wdr write_wdr read_flag write_flag read_limb
                          read_wsr write_wsr
                          set_pc update_state call_stack_pop call_stack_push
                          length hd_error tl skipn nth_error fold_left
                          fetch fetch_ctx Nat.add fst snd lookup_wdr
                          err random option_bind proof_semantics
                          repeat_advance_pc advance_pc assert_or_error]
               | progress cbv [gpr_has_value write_wdr update_mlz write_flag
                                 word32_binop word32_unop word256_binop]
               | eassumption ]
  end.
Ltac simplify_side_condition := repeat simplify_side_condition_step.

Ltac get_next_insn :=
  lazymatch goal with
  | |- eventually (run1 (fetch:=?fetch)) _ (otbn_busy ?pc _ _ _ _ _ _) =>
      let i := eval vm_compute in (fetch pc) in
        i
  end.

(* Debugging tactic, prints the next instruction to be fetched. *)
Ltac print_next_insn :=
  let i := ltac:(get_next_insn) in
  idtac i.

(* Finds the PC that matches the end of the loop. *)
Ltac find_loop_end' fetch pc :=
  let i := eval vm_compute in (fetch pc) in
    match i with
    | Some (Control (LoopEnd _)) => pc
    | Some (Control (Loop _)) =>
        let end_pc := find_loop_end' fetch (advance_pc pc) in
        find_loop_end' fetch (advance_pc end_pc)
    | Some (Control (Loopi _)) =>
        let end_pc := find_loop_end' fetch (advance_pc pc) in
        find_loop_end' fetch (advance_pc end_pc)
    | Some _ => find_loop_end' fetch (advance_pc pc)
    | None => fail "reached end of function without finding loop end"
    end.
Ltac find_loop_end :=
  lazymatch goal with
  | |- context [eventually (run1 (fetch:=?fetch)) _ (otbn_busy ?pc _ _ _ _ _ _)] =>
      let i := eval vm_compute in (fetch pc) in
        match i with
        | Some (Control (Loop _)) => find_loop_end' fetch (advance_pc pc)
        | Some (Control (Loopi _)) => find_loop_end' fetch (advance_pc pc)
        | ?x => fail "expected a loop insn at " pc ", got " x
        end
  | _ => fail "could not determine fetch and pc from goal"
  end.

Ltac straightline_step :=
  init_register_tracking_if_missing;
  let i := get_next_insn in
  lazymatch i with
  | Some (Straightline _) =>
      intros; subst; eapply eventually_step_cps;
      simplify_side_condition; intros; subst;
      lazymatch goal with
      | |- eventually run1 _ _ => idtac
      | _ => fail "straightline_step: failed to prove side conditions!"
               "Try `eapply eventually_step_cps; simplify_side_condition`"
               "to see what was left over"
      end; track_registers_update
  | Some ?i => fail "next instruction is not straightline:" i
  | None => fail "pc is invalid?"
  end.
