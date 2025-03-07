Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import coqutil.Z.ZLib.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Util.Map.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Weakening.
Require Import Otbn.Util.Tactics.Zsimplify.
Import ListNotations.
Local Open Scope Z_scope.

(*** Helper lemmas for proving things about programs. ***)

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.

  Definition gpr_has_value (regs : regfile) (r : gpr) (v : word32) : Prop :=
    read_gpr regs r (eq v).

  Definition function_symbols_disjoint (fn1 fn2 : otbn_function) : Prop :=
    let name1 := fst (fst fn1) in
    let name2 := fst (fst fn2) in
    let syms1 := snd (fst fn1) in
    let syms2 := snd (fst fn2) in
    map.disjoint syms1 syms2
    /\ map.get syms1 name2 = None
    /\ map.get syms2 name1 = None
    /\ name1 <> name2.    

  Lemma fetch_fn_disjoint fn1 fn2 dst i :
    fetch_fn fn1 dst = Some i ->
    function_symbols_disjoint fn1 fn2 ->
    fetch_fn fn2 dst = None.
  Proof.
    cbv [function_symbols_disjoint].
    destruct fn1 as [[name1 syms1] insns1].
    destruct fn2 as [[name2 syms2] insns2].
    destruct dst as [dst offset].
    cbv [fetch_fn get_label_offset]. cbn [fst snd].
    repeat lazymatch goal with
           | |- context [String.eqb ?x ?y] => destr (String.eqb x y); subst; try congruence
           | |- context [match _ with _ => _ end] => destruct_one_match; try congruence
           | H0 : map.disjoint ?m1 ?m2,
               H1 : map.get ?m1 ?k = Some _,
                 H2 : map.get ?m2 ?k = Some _ |- _ =>
               exfalso; eapply H0; eauto
           | H : _ /\ _ |- _ => destruct H
           | H : ?x <> ?x |- _ => congruence
           | H : Some _ = None |- _ => congruence
           | _ => progress intros
           end.
  Qed.

  Lemma fetch_fn_name offset (fn : otbn_function) :
    fetch_fn fn (fst (fst fn), offset) = nth_error (snd fn) offset.
  Proof.
    cbv [fetch_fn get_label_offset]. cbn [fst snd].
    rewrite String.eqb_refl, Nat.add_0_l. reflexivity.
  Qed.
  
  Lemma fetch_fn_sym fn label offset label_offset :
    label <> fst (fst fn) ->
    map.get (snd (fst fn)) label = Some label_offset ->
    fetch_fn fn (label, offset) = nth_error (snd fn) (label_offset + offset).
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [fetch_fn get_label_offset]; cbn [fst snd]; intros.
    destr (label =? fn_name)%string; [ congruence | ].
    destruct_one_match; congruence.
  Qed.
  
  Lemma fetch_ctx_done :
    forall fns dst i,
      fold_left (fun res fn =>
                   match res, fetch_fn fn dst with
                   | None, Some i => Some i
                   | _, _ => res
                   end) fns (Some i) = Some i.
  Proof.
    induction fns; cbn [fold_left]; [ reflexivity | ].
    intros. apply IHfns.
  Qed.

  Lemma fetch_fn_Some fn pc i :
      fetch_fn fn pc = Some i ->
      exists offset,
        get_label_offset fn (fst pc) = Some offset
        /\ nth_error (snd fn) (offset + snd pc) = Some i.
  Proof.
    cbv [fetch_fn]. destruct_one_match; [ | congruence ].
    intros. eexists; ssplit; [ reflexivity .. | ].
    assumption.
  Qed.

  Lemma fetch_ctx_Some :
    forall fns pc i,
      fetch_ctx fns pc = Some i ->    
      exists fn,
        fetch_fn fn pc = Some i
        /\ In fn fns.
  Proof.
    cbv [fetch_ctx].
    induction fns as [|fn fns]; cbn [fold_left]; [ congruence | ].
    intros. destruct_one_match_hyp.
    { rewrite fetch_ctx_done in *.
      lazymatch goal with H : Some _ = Some _ |- _ => inversion H; clear H; subst end.
      eexists; ssplit; eauto using in_eq. }
    { repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : fold_left _ _ None = Some _ |- _ => apply IHfns in H
             end.
      eexists; ssplit; eauto using in_cons. }
  Qed.

  Lemma fetch_ctx_singleton_iff fn dst i :
    fetch_ctx [fn] dst = Some i <-> fetch_fn fn dst = Some i.
  Proof.
    cbn [fetch_ctx fold_left]. destruct_one_match; split; congruence.
  Qed.

  Lemma fetch_ctx_cons_eq fns fn dst i :
      fetch_ctx [fn] dst = Some i ->
      fetch_ctx (fn :: fns) dst = Some i.
  Proof.
    cbn [fetch_ctx fold_left]; intro Hfn.
    rewrite Hfn. eauto using fetch_ctx_done.
  Qed.

  (* TODO: rework this lemma so it's easier -- not just fetch_fn =
     None, but fn is disjoint from the symbol table *)
  Lemma fetch_ctx_cons_ne fns fn dst :
    fetch_fn fn dst = None ->
    fetch_ctx (fn :: fns) dst = fetch_ctx fns dst.
  Proof.
    cbn [fetch_ctx fetch_fn fold_left]; intro Hfn.
    rewrite Hfn. eauto.
  Qed.

  Lemma eventually_jump
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
    forall dst pc (regs : regfile) wregs flags dmem cstack lstack spec post,
      fetch2 pc = Some (Control (Jal x1 dst)) ->
      (length cstack < 8)%nat ->
      returns (fetch:=fetch1) dst regs wregs flags dmem (advance_pc pc :: cstack) lstack spec ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      (forall regs wregs flags dmem,
          spec regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch2))
            post (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch2)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    cbv [returns]; intros.
    cbn [hd_error] in *.
    eapply eventually_step.
    { cbv [run1]; intros. eexists; split; [ eassumption | ].
      cbv iota. cbn [ctrl1 call_stack_push set_pc].
      destruct_one_match; try lia; apply eq_refl. }
    intros; subst.
    eapply eventually_trans;
      [ eapply fetch_weaken; eauto | intro st; destruct st; try contradiction ].
    intros; repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end. subst.
    cbn [tl]. eauto.
  Qed.
    
  Lemma eventually_invariant {label : Type} {fetch : label * nat -> option insn} :
    forall (invariant : nat -> otbn_state -> Prop) iters post st,
      invariant iters st ->
      (forall i st,
          (0 <= i < iters)%nat ->
          invariant (S i) st ->
          eventually (run1 (fetch:=fetch)) (fun st => invariant i st \/ post st) st) ->
      (forall st, invariant 0%nat st -> eventually (run1 (fetch:=fetch)) post st) ->
      eventually (run1 (fetch:=fetch)) post st.
  Proof.
    induction iters; intros; [ solve [eauto] | ].
    apply (eventually_trans _ (fun st => invariant iters st \/ post st));
      repeat match goal with
        | H : _ \/ _ |- _ => destruct H
        | H : context [invariant] |- _ => apply H; auto; lia
        | _ => eapply IHiters; eauto; [ ]
        | _ => progress intros
        | _ => eauto using eventually_done
        end.
  Qed.

  (* Loop invariant helper lemma. Note: `invariant i` should hold on
     the state the loop has when it reaches the end of the loop body
     in the `i`th iteration from last, so e.g. `invariant 0` should
     hold at the very end of the loop. *)
  Lemma loop_invariant
    {label : Type} {fetch : label * nat -> option insn} :
    forall (invariant : nat -> regfile -> wregfile -> flagfile -> mem -> Prop)
           (end_pc : label * nat)
           iters pc r v (regs : regfile) wregs flags dmem cstack lstack post,
      fetch pc = Some (Control (Loop r)) ->
      fetch end_pc = Some (Control LoopEnd) ->
      gpr_has_value regs r v ->
      Z.of_nat iters = word.unsigned v ->
      (length lstack < 8)%nat ->
      iters <> 0%nat ->
      invariant iters regs wregs flags dmem ->
      (* invariant step condition; if `invariant` holds at start, we reach end *)
      (forall i regs wregs flags dmem,
          (0 <= i < iters)%nat ->
          invariant (S i) regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch))
          (fun st => (exists regs wregs flags dmem,
                         invariant i regs wregs flags dmem
                         /\ st = match i with
                                 | S i => otbn_busy (advance_pc pc) regs wregs flags dmem cstack
                                            ((advance_pc pc, i) :: lstack)
                                 | O => otbn_busy (advance_pc end_pc)
                                          regs wregs flags dmem cstack lstack
                                 end)
                     \/ post st)
          (otbn_busy (advance_pc pc) regs wregs flags dmem cstack
             ((advance_pc pc, i) :: lstack))) ->
      (forall regs wregs flags dmem,
          invariant 0%nat regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch)) post
            (otbn_busy (advance_pc end_pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    cbv [loop_start]; intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct iters; [ lia | ].    
    eapply eventually_step.
    { cbn [run1]. eexists; ssplit; [ eassumption | ].
      cbv iota. cbn [ctrl1 read_gpr_from_state].
      eapply read_gpr_weaken; [ eassumption | ].
      intros; cbv [loop_start]. ssplit; [ lia .. | ].
      subst.
      lazymatch goal with H : Z.of_nat _ = word.unsigned ?v |- context [word.unsigned ?v] =>
                            rewrite <-H end.
      rewrite Nat2Z.id.
      destruct_one_match; try lia; eapply eq_refl. }
    intros; subst.
    eapply eventually_invariant
      with (iters := S iters)
           (invariant :=
              fun i st =>
                (exists regs wregs flags dmem,
                    invariant i regs wregs flags dmem
                    /\ st = match i with
                            | S i => otbn_busy (advance_pc pc) regs wregs flags dmem cstack
                                       ((advance_pc pc, i) :: lstack)
                            | O => otbn_busy (advance_pc end_pc) regs wregs flags dmem cstack lstack
                            end)).
    { intros. subst. eexists; ssplit; eauto. }
    { intros. subst.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | H : context [eventually run1 (fun st => _ \/ post st)] |- _ =>
                 apply H; eauto; lia
             | _ => progress subst
             end. }
    { intros. subst.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | _ => progress subst
             end.
      eauto. }
  Qed.

  Lemma eventually_beq {label : Type} {fetch : label * nat -> option insn}:
    forall pc dst r1 r2 regs wregs flags dmem cstack lstack v1 v2 post,
      fetch pc = Some (Control (Beq r1 r2 dst)) ->
      gpr_has_value regs r1 v1 ->
      gpr_has_value regs r2 v2 ->
      (* branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (dst, 0%nat) regs wregs flags dmem cstack lstack)) ->
      (* no-branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros.
    destr (word.eqb v1 v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        rewrite word.eqb_eq by reflexivity.
        cbv [set_pc]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_bne {label : Type} {fetch : label * nat -> option insn}:
    forall pc dst r1 r2 regs wregs flags dmem cstack lstack v1 v2 post,
      fetch pc = Some (Control (Bne r1 r2 dst)) -> 
      gpr_has_value regs r1 v1 ->
      gpr_has_value regs r2 v2 ->
      (* branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (dst, 0%nat) regs wregs flags dmem cstack lstack)) ->
      (* no-branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros.
    destr (word.eqb v1 v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_loop_end {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack loop_start iters post,
      fetch pc = Some (Control LoopEnd) ->
      (match iters with
       | O => eventually (run1 (fetch:=fetch)) post
                (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)
       | S iters => eventually (run1 (fetch:=fetch)) post
                      (otbn_busy loop_start regs wregs flags dmem cstack
                         ((loop_start, iters) :: lstack))
       end) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack ((loop_start, iters) :: lstack)).
  Proof.
    intros. destruct iters.
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbn [loop_end hd_error tl ctrl1].
        do 2 eexists; ssplit; [ reflexivity .. | ].
        cbv iota. apply eq_refl. }
      intros; subst. eassumption. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbn [loop_end hd_error tl ctrl1].
        do 2 eexists; ssplit; [ reflexivity .. | ].
        cbv iota. apply eq_refl. }
      intros; subst. eassumption. }
  Qed.

  Lemma eventually_ret {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack ret_pc post,
      fetch pc = Some (Control Ret) ->
      hd_error cstack = Some ret_pc ->
      post (otbn_busy ret_pc regs wregs flags dmem (tl cstack) lstack) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbn [ctrl1 call_stack_pop]. eexists; ssplit; [ eassumption .. | ].
      apply eq_refl. }
    intros; subst. eauto using eventually_done.
  Qed.

  Lemma eventually_ecall {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack post,
      fetch pc = Some (Control Ecall) ->
      post (otbn_done pc dmem) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbn [ctrl1 program_exit]. eassumption. }
    intros; subst. eauto using eventually_done.
  Qed.

  Lemma eventually_straightline
    {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack i post,
      fetch pc = Some (Straightline i) ->
      strt1 regs wregs flags dmem i
        (fun regs wregs flags dmem =>
           eventually (run1 (fetch:=fetch)) post
             (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbv iota. cbv [update_state set_pc]. eassumption. }
    intros; subst. eauto.
  Qed.

  Lemma is_word_aligned_imm width imm :
    0 <= width <= 32 ->
    is_word_aligned (2^width) (word.of_Z imm) = true <-> (imm mod 2^width = 0).
  Proof.
    cbv [is_word_aligned]. intros.
    pose proof Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia).
    assert (2^width <= 2^32) by (apply Z.pow_le_mono; lia).
    assert (0 <= Z.ones width < 2^32) by (rewrite Z.ones_equiv; split; lia).
    rewrite word.unsigned_eqb, Z.eqb_eq.
    rewrite word.unsigned_of_Z_0, word.unsigned_and.
    replace (2^width - 1) with (Z.ones width) by (rewrite Z.ones_equiv; lia).
    rewrite (word.unsigned_of_Z_nowrap (Z.ones width)) by lia.
    rewrite Z.land_ones by lia.
    rewrite word.unsigned_of_Z.
    cbv [word.wrap]. pose proof Z.mod_pos_bound (imm mod 2^32) (2^width) ltac:(lia).
    rewrite Z.mod_small by lia.
    replace (2^32) with (2^width * (2^(32-width)))
      by (rewrite <-Z.pow_add_r by lia; apply f_equal; lia).
    rewrite Z.rem_mul_r by lia.
    Z.push_mod. zsimplify. Z.push_pull_mod. split; lia.
  Qed.

  Lemma is_word32_aligned_imm imm :
    is_word_aligned 4 (word.of_Z imm) = true <-> (imm mod 4 = 0).
  Proof. apply (is_word_aligned_imm 2). lia. Qed.

  Lemma is_word256_aligned_imm imm :
    is_word_aligned 32 (word.of_Z imm) = true <-> (imm mod 32 = 0).
  Proof. apply (is_word_aligned_imm 5). lia. Qed.

  Lemma is_word_aligned_0 width :
    is_word_aligned width (word.of_Z 0) = true.
  Proof.
    cbv [is_word_aligned]. intros. apply word.eqb_eq, word.unsigned_inj.
    rewrite word.unsigned_and, !word.unsigned_of_Z_0.
    rewrite Z.land_0_l. cbv [word.wrap]. rewrite Z.mod_0_l; lia.
  Qed.

  Lemma is_word_aligned_add width addr offset :
    0 <= width <= 32 ->
    is_word_aligned (2^width) addr = true ->
    is_word_aligned (2^width) offset = true ->
    is_word_aligned (2^width) (word.add addr offset) = true.
  Proof.
    cbv [is_word_aligned]; intros. apply word.eqb_eq.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : word.eqb ?x ?y = true |- _ =>
               rewrite word.unsigned_eqb in H
           | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
           end.
    apply word.unsigned_inj.
    rewrite !word.unsigned_of_Z_0 in * by lia.
    rewrite !word.unsigned_and, !word.unsigned_add in *.
    pose proof Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia).
    assert (2^width <= 2^32) by (apply Z.pow_le_mono; lia).
    rewrite !word.unsigned_of_Z_nowrap in * by lia.
    replace (2^width - 1) with (Z.ones width) in * by (rewrite Z.ones_equiv; lia).
    rewrite !Z.land_ones in * by lia.
    cbv [word.wrap] in *.
    repeat lazymatch goal with
           | |- context [(?x mod 2^width) mod 2^32] =>
               pose proof Z.mod_pos_bound x (2^width) ltac:(lia);
               rewrite (Z.mod_small (x mod (2^width)) (2^32)) by lia
           | H: context [(?x mod 2^width) mod 2^32] |- _ =>
               pose proof Z.mod_pos_bound x (2^width) ltac:(lia);
               rewrite (Z.mod_small (x mod (2^width)) (2^32)) in H by lia
           end.
    replace (2^32) with (2^width * (2^(32-width)))
      by (rewrite <-Z.pow_add_r by lia; apply f_equal; lia).
    rewrite Z.rem_mul_r by lia.
    Z.push_mod. zsimplify.
    rewrite Z.add_mod by lia.
    repeat lazymatch goal with H : 0 = ?x |- context [?x] => rewrite <-H end.
    rewrite Z.mod_0_l by lia. reflexivity.
  Qed.

  Lemma is_word32_aligned_add addr offset :
    is_word_aligned 4 addr = true ->
    is_word_aligned 4 offset = true ->
    is_word_aligned 4 (word.add addr offset) = true.
  Proof. apply (is_word_aligned_add 2). lia. Qed.

  Lemma is_word256_aligned_add addr offset :
    is_word_aligned 32 addr = true ->
    is_word_aligned 32 offset = true ->
    is_word_aligned 32 (word.add addr offset) = true.
  Proof. apply (is_word_aligned_add 5). lia. Qed.
  
  Lemma store_bytes_step dmem addr (bs : list byte) (P : mem -> Prop) old_bs R :
    word.unsigned addr + Z.of_nat (length bs) < DMEM_BYTES ->
    length old_bs = length bs ->
    (bytes_at addr old_bs * R)%sep dmem ->
    (forall dmem, (bytes_at addr bs * R)%sep dmem -> P dmem) ->
    store_bytes dmem addr bs P.
  Proof.
    pose proof word.unsigned_range addr.
    assert (DMEM_BYTES < 2^32) by (cbv [DMEM_BYTES]; lia).
    generalize dependent dmem. generalize dependent addr.
    generalize dependent P. generalize dependent R. generalize dependent old_bs.    
    induction bs; destruct old_bs; cbn [store_bytes length] in *; try lia;
      cbv [store_byte]; intros;
      repeat lazymatch goal with
        | H : context [map.of_list_word_at _ nil] |- _ =>
            rewrite map.of_list_word_nil in H
        | H : context [map.of_list_word_at _ (cons _ _)] |- _ =>
            rewrite map.of_list_word_at_cons in H
        | |- context [map.of_list_word_at _ nil] => rewrite map.of_list_word_nil
        | |- context [map.of_list_word_at _ (cons _ _)] => rewrite map.of_list_word_at_cons
        | H : length ?x = 0%nat |- _ => apply length_zero_iff_nil in H; subst
        | |- store_bytes _ _ bs _ =>
            eapply IHbs with (R:=sep R (ptsto _ _)) (old_bs:=old_bs); intros
        | H : forall m, _ -> ?P m |- ?P _ => eapply H
        | |- if ?x <? ?y then _ else _ => destr (x <? y); try lia
        | |- context [word.unsigned (word.add _ _)] => rewrite word.unsigned_add
        | |- context [word.unsigned (word.of_Z 1)] => rewrite word.unsigned_of_Z_1
        | |- context [word.wrap (word.unsigned ?addr + 1)] =>
            cbv [word.wrap]; rewrite Z.mod_small by lia
        | |- _ /\ _ => ssplit            
        | H : ?P |- ?P => exact H
        | _ => first [ progress extract_ex1_and_emp_in_hyps
                     | progress extract_ex1_and_emp_in_goal
                     | lazymatch goal with
                       | |- _ < _ => lia
                       | |- _ <= _ => lia
                       | |- length _ = length _ => lia
                       | _ => fail
                       end ]
        end.
    { apply sep_assoc, sep_comm. eapply sep_put.
      use_sep_assumption. rewrite sep_put_iff1; [ ecancel | ].
      eapply map.of_list_word_at_get_pred. lia. }
    { seprewrite sep_put_iff1; [ | use_sep_assumption; ecancel ].
      eapply map.of_list_word_at_get_pred. lia. }
  Qed.
  
  Lemma store_word_step
    {width} {word : word.word width} {word_ok : word.ok word}
    dmem addr (v old_v : word) (P : mem -> Prop) R :
    is_word_aligned (width / 8) addr = true ->
    word.unsigned addr + width / 8 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.
    intros. subst.
    pose proof word.width_pos (word:=word).
    cbv [store_word]. destruct_one_match; [ | congruence ].
    eapply store_bytes_step.
    { rewrite length_le_split.
      rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    { rewrite !length_le_split. reflexivity. }    
    { use_sep_assumption. cbv [word_at]. ecancel. }
    { intros. lazymatch goal with H : forall m, _ -> P m |- P _ => apply H end.
      use_sep_assumption. cbv [word_at]. ecancel. }
  Qed.
  
  Lemma store_word32_step
    dmem addr (v old_v : word32) (P : mem -> Prop) R :
    is_word_aligned 4 addr = true ->
    word.unsigned addr + 4 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.  intros; eapply store_word_step; eauto. Qed.
  
  Lemma store_word256_step
    dmem addr (v old_v : word256) (P : mem -> Prop) R :
    is_word_aligned 32 addr = true ->
    word.unsigned addr + 32 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.  intros; eapply store_word_step; eauto. Qed.

  Lemma load_bytes_step dmem addr bs len (P : _ -> Prop) R :
    word.unsigned addr + Z.of_nat len < DMEM_BYTES ->
    (bytes_at addr bs * R)%sep dmem ->
    length bs = len ->
    P bs ->
    load_bytes dmem addr len P.
  Proof.
    assert (DMEM_BYTES < 2^32) by (cbv [DMEM_BYTES]; lia).
    generalize dependent addr. generalize dependent bs. generalize dependent P.
    generalize dependent R.
    induction len; destruct bs; cbn [load_bytes length] in *; try lia; eauto; [ ].
    intros. cbv [load_byte]. destruct_one_match; try lia; [ ].
    cbn [option_bind proof_semantics].
    pose proof word.unsigned_range addr.
    lazymatch goal with
      | H : sep (eq (map.of_list_word_at _ (_ :: _))) _ _ |- _ =>
          rewrite map.of_list_word_at_cons in H;
          seprewrite_in sep_put_iff1 H
    end; [ | ].
    { eapply map.of_list_word_at_get_pred. lia. }
    { eexists.
      ssplit; [ eapply get_sep; use_sep_assumption; ecancel | ].
      eapply IHlen with (R:=sep _ R); try eassumption; try lia; [ | ].
      { rewrite word.unsigned_add, word.unsigned_of_Z_1.
        cbv [word.wrap]. rewrite Z.mod_small by lia. lia. }
      { use_sep_assumption. ecancel. } }
  Qed.

  Lemma load_word_step
    {width} {word : word.word width} {word_ok : word.ok word}
    dmem addr (v : word) (P : _ -> Prop) R :
    width mod 8 = 0 ->
    is_word_aligned (width / 8) addr = true ->
    word.unsigned addr + width / 8 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof.
    intros. pose proof word.width_pos (word:=word).
    cbv [load_word]. destruct_one_match; [ | congruence ].
    eapply load_bytes_step.
    { rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    { use_sep_assumption. cbv [word_at]. ecancel. }
    { rewrite !length_le_split. reflexivity. }
    { intros. pose proof Z.div_pos width 8 ltac:(lia) ltac:(lia).
      rewrite le_combine_split. rewrite Z2Nat.id by lia.
      rewrite Z.div_mul_undo by lia.
      rewrite Z.mod_small by (apply word.unsigned_range).
      rewrite word.of_Z_unsigned. assumption. }
  Qed.

  Lemma load_word32_step dmem addr (v :word32) (P : _ -> Prop) R :
    is_word_aligned 4 addr = true ->
    word.unsigned addr + 4 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof. intros; eapply load_word_step; eauto. Qed.

  Lemma load_word256_step dmem addr (v :word256) (P : _ -> Prop) R :
    is_word_aligned 32 addr = true ->
    word.unsigned addr + 32 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof. intros; eapply load_word_step; eauto. Qed.

  Lemma read_wdr_indirect_step i wregs (P : _ -> Prop) :
    (exists w, lookup_wdr i = w /\ read_wdr wregs w P) ->
    read_wdr_indirect i wregs P.
  Proof. cbv [read_wdr_indirect]; intros [? [? ?]]. subst. eauto. Qed.

  Lemma write_wdr_indirect_step i wregs v (P : _ -> Prop) :
    (exists w, lookup_wdr i = w /\ write_wdr wregs w v P) ->
    write_wdr_indirect i wregs v P.
  Proof. cbv [write_wdr_indirect]; intros [? [? ?]]. subst. eauto. Qed.
  

  Lemma lookup_wdr_li imm :
    0 <= imm < 32 ->
    lookup_wdr (addi_spec (word.of_Z 0) imm) = lookup_wdr' (Z.to_nat imm).
  Proof.
    cbv [lookup_wdr addi_spec]; intros.
    destruct_one_match; try lia; [ ]. do 2 apply f_equal.
    rewrite word.add_0_l.
    rewrite word.unsigned_and, !word.unsigned_of_Z_nowrap by lia.
    change 31 with (Z.ones 5).
    rewrite Z.land_ones by lia. change (2^5) with 32.
    rewrite Z.mod_small by lia. cbv [word.wrap].
    apply Z.mod_small; lia.
  Qed.

  Lemma apply_shift_0 x P : P x -> apply_shift x 0 P.
  Proof.
    intros; cbv [apply_shift is_valid_arith256_shift_imm].
    change (Z.abs 0) with 0. rewrite Z.mod_0_l by lia.
    repeat destruct_one_match; try lia. eauto.
  Qed.

  Lemma apply_shiftl x s P :
    0 < s <= 248 ->
    s mod 8 = 0 ->
    P (word.slu x (word.of_Z s)) ->
    apply_shift x s P.
  Proof.
    intros; cbv [apply_shift is_valid_arith256_shift_imm].
    rewrite Z.abs_eq by lia.
    repeat destruct_one_match; try lia; eauto.
  Qed.

  Lemma apply_shiftr x s P :
    0 < s <= 248 ->
    s mod 8 = 0 ->
    P (word.sru x (word.of_Z s)) ->
    apply_shift x (-s) P.
  Proof.
    intros; cbv [apply_shift is_valid_arith256_shift_imm].
    rewrite Z.abs_opp, Z.abs_eq by lia.
    repeat destruct_one_match; try lia; eauto.
  Qed.
  
  Lemma carry_bit_add_div x y :
    0 <= x < 2^256 ->
    0 <= y < 2^256 ->
    Z.b2z (carry_bit (x + y)) = (x + y) / 2^256.
  Proof.
    intros. cbv [carry_bit].
    pose proof Z.div_small (x + y) (2^256).
    pose proof Z.div_lt_upper_bound (x + y) (2^256) 2 ltac:(lia) ltac:(lia).
    pose proof Z.div_le_lower_bound (x + y) (2^256) 1 ltac:(lia).
    cbv [Z.b2z] in *; repeat destruct_one_match; lia.
  Qed.
  
  Lemma carry_bit_addc_div x y c :
    0 <= x < 2^256 ->
    0 <= y < 2^256 ->
    Z.b2z (carry_bit (x + y + Z.b2z c)) = (x + y + Z.b2z c) / 2^256.
  Proof.
    intros. cbv [carry_bit].
    pose proof Z.div_small (x + y + Z.b2z c) (2^256).
    assert (0 <= Z.b2z c < 2) by (destr c; cbn; lia).
    pose proof Z.div_lt_upper_bound (x + y + Z.b2z c) (2^256) 2 ltac:(lia) ltac:(lia).
    pose proof Z.div_le_lower_bound (x + y + Z.b2z c) (2^256) 1 ltac:(lia).
    cbv [Z.b2z] in *; repeat destruct_one_match; lia.    
  Qed.

  Lemma word_xor_same {width : Z} {word : word width} {word_ok : word.ok word} :
    forall x : word, word.xor x x = word.of_Z 0.
  Proof.
    intros. apply word.unsigned_inj.
    rewrite word.unsigned_xor, word.unsigned_of_Z_0.
    rewrite Z.lxor_nilpotent. pose proof word.modulus_pos.
    apply Z.mod_0_l. lia.
  Qed.
End __.
