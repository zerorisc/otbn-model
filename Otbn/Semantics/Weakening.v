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
Require Import Otbn.Util.Tactics.Zsimplify.
Import ListNotations.
Local Open Scope Z_scope.

(*** Lemmas for CPS-style routines that allow weakening the postcondition. ***)

Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  
  Lemma read_gpr_weaken regs r P Q :
    read_gpr regs r P ->
    (forall regs, P regs -> Q regs) ->
    read_gpr regs r Q.
  Proof.
    cbv [read_gpr err option_bind proof_semantics]; intros; destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma read_wdr_weaken wregs r P Q :
    read_wdr wregs r P ->
    (forall wregs, P wregs -> Q wregs) ->
    read_wdr wregs r Q.
  Proof.
    cbv [read_wdr err option_bind proof_semantics]; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma read_flag_weaken flags f P Q :
    read_flag flags f P ->
    (forall flags, P flags -> Q flags) ->
    read_flag flags f Q.
  Proof.
    cbv [read_flag err option_bind proof_semantics]; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma read_wsr_weaken wregs r P Q :
    read_wsr wregs r P ->
    (forall x, P x -> Q x) ->
    read_wsr wregs r Q.
  Proof.
    cbv [read_wsr random urandom option_bind proof_semantics];
      intros.
    destruct r;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma read_csr_weaken regs flags r P Q :
    read_csr regs flags r P ->
    (forall x, P x -> Q x) ->
    read_csr regs flags r Q.
  Proof.
    cbv [read_csr read_flag read_flag_group err random urandom option_bind proof_semantics];
      intros.
    destruct r;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma read_limb_weaken wregs r P Q :
    read_limb wregs r P ->
    (forall x, P x -> Q x) ->
    read_limb wregs r Q.
  Proof.
    cbv [read_limb]; intros. repeat destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto using read_wdr_weaken]
        end.
  Qed.

  Lemma read_gpr_inc_weaken regs r P Q :
    read_gpr_inc regs r P ->
    (forall x, P x -> Q x) ->
    read_gpr_inc regs r Q.
  Proof.
    cbv [read_gpr_inc]; intros. repeat destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto using read_gpr_weaken]
        end.
  Qed.

  Lemma load_bytes_weaken dmem addr len P Q :
    load_bytes (T:=Prop) dmem addr len P ->
    (forall x, P x -> Q x) ->
    load_bytes (T:=Prop) dmem addr len Q.
  Proof.
    intros; generalize dependent addr. generalize dependent P. generalize dependent Q.
    induction len; cbn [load_bytes]; [ solve [auto] | ].
    intros. cbv [option_bind proof_semantics] in *.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : False |- _ => contradiction H
           | |- exists _, _ => eexists; ssplit; [ eassumption | ]
           | _ => solve [eauto]
           end.
    eapply IHlen; eauto; cbv beta; intros; eauto.
  Qed.

  Lemma load_word_weaken {width} {word} dmem addr P Q :
    load_word (width:=width) (word:=word) dmem addr P ->
    (forall x, P x -> Q x) ->
    load_word (width:=width) (word:=word) dmem addr Q.
  Proof.
    cbv [load_word]; intros. eapply load_bytes_weaken; eauto.
  Qed.

  Lemma store_bytes_weaken dmem addr bs P Q :
    store_bytes (T:=Prop) dmem addr bs P ->
    (forall x, P x -> Q x) ->
    store_bytes (T:=Prop) dmem addr bs Q.
  Proof.
    intros; generalize dependent addr. generalize dependent dmem.
    generalize dependent P. generalize dependent Q.
    induction bs; cbn [store_bytes]; [ solve [auto] | ].
    intros. eapply IHbs; eauto.
  Qed.

  Lemma store_word_weaken {width} {word} dmem addr v P Q :
    store_word (T:=Prop) (width:=width) (word:=word) dmem addr v P ->
    (forall x, P x -> Q x) ->
    store_word (T:=Prop) (width:=width) (word:=word) dmem addr v Q.
  Proof.
    cbv [store_word]. eapply store_bytes_weaken; eauto.
  Qed.

  Lemma write_gpr_weaken regs r v P Q :
    write_gpr regs r v P ->
    (forall regs, P regs -> Q regs) ->
    write_gpr regs r v Q.
  Proof.
    cbv [write_gpr err proof_semantics]; intros; destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma write_wdr_weaken wregs r v P Q :
    write_wdr (T:=Prop) wregs r v P ->
    (forall wregs, P wregs -> Q wregs) ->
    write_wdr (T:=Prop) wregs r v Q.
  Proof.
    cbv [write_wdr write_flag_group extract_flag]; intros. eauto.
  Qed.

  Lemma write_wsr_weaken wregs r v P Q :
    write_wsr (T:=Prop) wregs r v P ->
    (forall wregs, P wregs -> Q wregs) ->
    write_wsr (T:=Prop) wregs r v Q.
  Proof.
    cbv [write_wsr]; intros; destruct_one_match; eauto.
  Qed.

  Lemma write_csr_weaken regs flags r v P Q :
    write_csr (T:=Prop) regs flags r v P ->
    (forall flags, P flags -> Q flags) ->
    write_csr (T:=Prop) regs flags r v Q.
  Proof.
    cbv [write_csr write_flag_group extract_flag]; intros; destruct_one_match; eauto.
  Qed.

  Lemma apply_shift_weaken v shift P Q :
    apply_shift v shift P ->
    (forall v, P v -> Q v) ->
    apply_shift v shift Q.
  Proof.
    cbv [apply_shift]; intros; repeat destruct_one_match; eauto.
  Qed.

  Lemma write_flag_weaken flags f v P Q :
    write_flag (T:=Prop) flags f v P ->
    (forall flags, P flags -> Q flags) ->
    write_flag (T:=Prop) flags f v Q.
  Proof.
    cbv [write_flag]; intros; repeat destruct_one_match; eauto.
  Qed.

  Lemma increment_gprs_weaken regs x y xinc yinc P Q :
    increment_gprs regs x y xinc yinc P ->
    (forall x y, P x y -> Q x y) ->
    increment_gprs regs x y xinc yinc Q.
  Proof.
    cbv [increment_gprs]; intros. repeat destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- read_gpr _ _ _ => eapply read_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ => eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | _ => solve [eauto]
        end.
  Qed.

  Lemma update_mlz_weaken flags fg v P Q :
    update_mlz (T:=Prop) flags fg v P ->
    (forall flags, P flags -> Q flags) ->
    update_mlz (T:=Prop) flags fg v Q.
  Proof.
    cbv [update_mlz]; intros.
    repeat lazymatch goal with
           | |- write_flag _ _ _ _ =>
               eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
           | _ => solve [eauto]
           end.
  Qed.

  Lemma read_wdr_indirect_weaken i wregs P Q :
    read_wdr_indirect (T:=Prop) i wregs P ->
    (forall x, P x -> Q x) ->
    read_wdr_indirect (T:=Prop) i wregs Q.
  Proof. eapply read_wdr_weaken; eauto. Qed.

  Lemma write_wdr_indirect_weaken i wregs v P Q :
    write_wdr_indirect (T:=Prop) i wregs v P ->
    (forall x, P x -> Q x) ->
    write_wdr_indirect (T:=Prop) i wregs v Q.
  Proof. eapply write_wdr_weaken; eauto. Qed.

  Lemma assert_or_error_weaken err_bits cond err_code P Q :
    assert_or_error (T:=Prop) err_bits cond err_code P ->
    (forall x, P x -> Q x) ->
    assert_or_error (T:=Prop) err_bits cond err_code Q.
  Proof.
    cbv [assert_or_error]. destruct_one_match; eauto.
  Qed.

  Lemma strt1_weaken regs wregs flags dmem i P Q :
    strt1 regs wregs flags dmem i P ->
    (forall regs wregs flags dmem err_bits,
        P regs wregs flags dmem err_bits -> Q regs wregs flags dmem err_bits) ->
    strt1 regs wregs flags dmem i Q.
  Proof.
    cbv [strt1 err proof_semantics]; intros; repeat destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- assert_or_error _ _ _ _ =>
            eapply assert_or_error_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_gpr _ _ _ =>
            eapply read_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_wdr _ _ _ =>
            eapply read_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_flag _ _ _ =>
            eapply read_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_wsr _ _ _ =>
            eapply read_wsr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_limb _ _ _ =>
            eapply read_limb_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_gpr_inc _ _ _ =>
            eapply read_gpr_inc_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_bytes _ _ _ _ =>
            eapply load_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_word _ _ _ =>
            eapply load_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_bytes _ _ _ _ =>
            eapply store_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_word _ _ _ _ =>
            eapply store_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ =>
            eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wdr _ _ _ _ =>
            eapply write_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_csr _ _ _ _ _ =>
            eapply write_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wsr _ _ _ _ =>
            eapply write_wsr_weaken; [ eassumption | ]; cbv beta; intros
        | |- apply_shift _ _ _ =>
            eapply apply_shift_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_flag _ _ _ _ =>
            eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- increment_gprs _ _ _ _ _ _ =>
            eapply increment_gprs_weaken; [ eassumption | ]; cbv beta; intros
        | |- update_mlz _ _ _ _ =>
            eapply update_mlz_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_wdr_indirect _ _ _ =>
            eapply read_wdr_indirect_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wdr_indirect _ _ _ _ =>
            eapply write_wdr_indirect_weaken; [ eassumption | ]; cbv beta; intros
        | |- if ?x then _ else _ => destr x
        | |- Q _ _ _ _ _ => solve [eauto]
        | _ => progress cbv [word32_binop word32_unop word256_binop]
        end.
  Qed.

  Lemma fetch_weaken_run1
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
    forall st P,
      run1 (fetch:=fetch1) st P ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      run1 (fetch:=fetch2) st P.
  Proof.
    induction st; cbn [run1]; intros; auto; [ ].
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end.
    eauto.
  Qed.

  Lemma fetch_weaken
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
    forall st P,
      eventually (run1 (fetch:=fetch1)) P st ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      eventually (run1 (fetch:=fetch2)) P st.
  Proof.
    induction 1; intros; [ auto using eventually_done | ].
    eapply eventually_step; eauto using fetch_weaken_run1.
  Qed.
End __.
