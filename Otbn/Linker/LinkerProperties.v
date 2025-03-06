Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Otbn.Model.ISA.
Require Import Otbn.Linker.Linker.
Require Import Otbn.Util.Maybe.
Require Import Otbn.Model.Semantics.
Require Import Otbn.Model.SemanticsProperties.
Import ListNotations.
Import MaybeNotations.
Local Open Scope Z_scope.

Section __.
  Context {word32 : word.word 32} {regfile : map.map reg word32}.
  Context {word256 : word.word 256} {wregfile : map.map wreg word256}.
  Context {flagfile : map.map flag bool} {mem : map.map word32 byte}.
  Context {word32_ok : word.ok word32} {word256_ok : word.ok word256}.
  Local Open Scope maybe_scope.

  (* Returns the overall size of the program containing the functions
     and starting at the given offset. *)
  Definition program_size (start : nat) (fns : list otbn_function) : nat :=
    fold_left
      (fun offset fn =>
         let fn_insns := snd fn in
          (offset + length fn_insns)%nat)
      fns start.

  Lemma link_symbols'_step :
    forall start_syms start_offset fn fns syms1 syms2 end_offset1 end_offset2,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms1, end_offset1) ->
      link_symbols' syms1 end_offset1 fns = Ok (syms2, end_offset2) ->
      link_symbols' start_syms start_offset (fn :: fns) = Ok (syms2, end_offset2).
  Proof.
    cbv [link_symbols']; intros; cbn [maybe_fold_left bind]; maybe_simpl; congruence.
  Qed.

  Lemma link_symbols'_offset :
    forall fns start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      end_offset = program_size start_offset fns.
  Proof.
    cbv [link_symbols' program_size]; induction fns; cbn [maybe_fold_left fold_left]; intros;
      maybe_simpl; [ reflexivity | ].
    destruct_products; cbn [fst snd] in *.
    lazymatch goal with
    | H : link_symbols_for_function _ _ = _ |- _ => cbv [link_symbols_for_function] in H
    end.
    maybe_simpl; cbn [fst snd] in *. eauto.
  Qed.
  
  Lemma link_symbols'_inv :
    forall start_syms start_offset fn fns syms2 end_offset2,
      link_symbols' start_syms start_offset (fn :: fns) = Ok (syms2, end_offset2) ->
      exists syms1 end_offset1,
        link_symbols_for_function (start_syms, start_offset) fn = Ok (syms1, end_offset1)
        /\ end_offset2 = program_size end_offset1 fns
        /\ link_symbols' syms1 end_offset1 fns = Ok (syms2, end_offset2).
  Proof.
    cbv [link_symbols']; cbn [maybe_fold_left bind]; intros; maybe_simpl.
    destruct_products; cbn [fst snd] in *.
    repeat lazymatch goal with
           | H : context [link_symbols_for_function ?a ?b]
             |- context [link_symbols_for_function ?a ?b] =>
               destruct (link_symbols_for_function a b) as [[? ?]|]; cbn [bind]
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           | _ => solve [eauto using link_symbols'_offset]
           end.    
  Qed.

  Lemma link_symbols_for_function_size :
    forall fn start_syms start_offset syms size,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, size) ->
      size = (start_offset + length (snd fn))%nat.
  Proof.
    cbv [link_symbols_for_function]; intros; maybe_simpl; reflexivity.
  Qed.

  Lemma link_symbols'_size :
    forall fns start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      program_size start_offset fns = end_offset.
  Proof.
    cbv [program_size]; induction fns; intros;
      [ cbn [link_symbols' maybe_fold_left] in *; maybe_simpl; reflexivity | ].
    cbn [fold_left].
    repeat lazymatch goal with
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               eapply link_symbols'_inv in H
           | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
               apply link_symbols_for_function_size in H; subst
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | _ => subst; solve [eauto]
           end.
  Qed.

  Lemma add_symbol_no_overwrite start_syms label1 label_offset1 syms :
    add_symbol start_syms label1 label_offset1 = Ok syms ->
    (forall label2 label_offset2,
        map.get start_syms label2 = Some label_offset2 ->
        map.get syms label2 = Some label_offset2).
  Proof.
    cbv [add_symbol]; intros.
    destr (map.get start_syms label1); [ congruence | ].
    destr (string_dec label1 label2); subst; [ congruence | ].
    maybe_simpl. rewrite map.get_put_diff by congruence.
    auto.
  Qed.

  Lemma add_symbol_fail start_syms label label_offset1 label_offset2 :
    map.get start_syms label = Some label_offset1 ->
    exists msg,
      add_symbol start_syms label label_offset2 = Err msg.
  Proof.
    cbv [add_symbol]; intros. destruct_one_match; try congruence.
    eauto.
  Qed.

  Lemma merge_symbols_no_overwrite fn_syms global_offset global_syms :
    forall syms,
      merge_symbols global_offset global_syms fn_syms = Ok syms ->
      (forall label label_offset,
          map.get global_syms label = Some label_offset ->
          map.get syms label = Some label_offset).
  Proof.
    cbv [merge_symbols].
    lazymatch goal with
    | |- forall syms,
        map.fold _ _ _ = ?x -> ?Q =>
        apply (map.fold_spec (fun _ m => forall syms, m = x -> Q))
    end; intros; maybe_simpl; eauto using add_symbol_no_overwrite.
  Qed.

  Lemma link_symbols_for_function_no_overwrite :
    forall fn start_syms start_offset syms label label_offset end_offset,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      map.get start_syms label = Some label_offset ->
      map.get syms label = Some label_offset.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function]; cbn [bind fst snd]; intros.
    maybe_simpl. eauto using add_symbol_no_overwrite, merge_symbols_no_overwrite.
  Qed.

  Lemma link_symbols_for_function_name_fail :
    forall fn start_syms start_offset name label_offset,
      name = fst (fst fn) ->
      map.get start_syms name = Some label_offset ->
      exists msg,
        link_symbols_for_function (start_syms, start_offset) fn = Err msg.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function]; cbn [bind fst snd]; intros.
    subst. lazymatch goal with H : map.get _ _ = Some _ |- _ =>
                                 eapply add_symbol_fail in H; destruct H end.
    rewrite H. maybe_simpl. eauto.
  Qed.

  Lemma link_symbols'_no_overwrite :
    forall fns start_syms start_offset syms label label_offset end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      map.get start_syms label = Some label_offset ->
      map.get syms label = Some label_offset.
  Proof.
    cbv [program_size]; induction fns; intros;
      [ cbn [link_symbols' maybe_fold_left] in *; maybe_simpl; solve [auto] | ].
    repeat lazymatch goal with
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               eapply link_symbols'_inv in H
           | H : exists _, _ |- _ => destruct H; subst
           | H : _ /\ _ |- _ => destruct H; subst
           | _ => solve [eauto using link_symbols_for_function_no_overwrite]
           end.
  Qed.

  Lemma link_symbols'_name_fail fn name :
    forall fns start_syms start_offset label_offset,
      In fn fns ->
      name = fst (fst fn) ->
      map.get start_syms name = Some label_offset ->
      exists msg,
        link_symbols' start_syms start_offset fns = Err msg.
  Proof.
    cbv [program_size link_symbols']; induction fns; cbn [In]; intros;
      repeat lazymatch goal with
        | H : False |- _ => contradiction H
        | H : _ \/ _ |- _ => destruct H
        | H : map.get _ _ = Some _ |- context [link_symbols_for_function _ fn] =>
            eapply link_symbols_for_function_name_fail in H; [ | reflexivity .. ];
            destruct H as [? H]; rewrite H; maybe_simpl; solve [eauto]
        | _ => progress (cbn [maybe_fold_left]; subst)
        end; [ ].
    maybe_simpl; eauto.
    destruct_products; cbn [fst snd] in *.
    eauto using link_symbols_for_function_no_overwrite.
  Qed.

  Lemma add_symbol_correct start_syms label label_offset syms :
      add_symbol start_syms label label_offset = Ok syms ->
      map.get syms label = Some label_offset.
  Proof.
    cbv [add_symbol]; destruct_one_match; intros; maybe_simpl; auto using map.get_put_same.
  Qed.

  Lemma merge_symbols_correct fn_syms global_offset global_syms :
    forall syms,
      merge_symbols global_offset global_syms fn_syms = Ok syms ->
      (forall label label_offset,
          map.get fn_syms label = Some label_offset ->
          map.get syms label = Some (global_offset + label_offset)%nat).
  Proof.
    cbv [merge_symbols].
    apply map.fold_spec.
    { intros. rewrite map.get_empty in *. congruence. }
    { intros. maybe_simpl.
      repeat lazymatch goal with
             | H : map.get (map.put _ ?x _) ?y = Some _ |- _ =>
                 destr (String.eqb x y);
                 [ rewrite map.get_put_same in H
                 | rewrite map.get_put_diff in H by congruence ]
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             end;
        eauto using add_symbol_correct, add_symbol_no_overwrite. }
  Qed.

  Lemma get_label_offset_name fn name :
    name = fst (fst fn) ->
    get_label_offset fn name = Some 0%nat.
  Proof.
    intros; subst. cbv [get_label_offset].
    destruct_one_match; congruence.
  Qed.

  Lemma link_symbols_for_function_correct
    fn start_syms start_offset syms end_offset dst fn_offset :
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      get_label_offset fn dst = Some fn_offset ->
      map.get syms dst = Some (start_offset + fn_offset)%nat.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function get_label_offset].
    cbn [bind fst snd]; intros; maybe_simpl.
    destruct_one_match_hyp; [ | solve [eauto using merge_symbols_correct] ].
    lazymatch goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end.
    rewrite Nat.add_0_r.
    eauto using add_symbol_correct, merge_symbols_no_overwrite.
  Qed.

  Lemma link_symbols_for_function_name fn start_syms start_offset syms end_offset :
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some start_offset.
  Proof.
    intros. replace start_offset with (start_offset + 0)%nat by lia.
    eapply link_symbols_for_function_correct; eauto; [ ].
    apply get_label_offset_name; reflexivity.
  Qed.

  Lemma link_symbols'_correct :
    forall fns1 fns2 fn start_syms start_offset syms end_offset fn_offset dst,
    link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = inl (syms, end_offset) ->
    get_label_offset fn dst = Some fn_offset ->
    map.get syms dst = Some (program_size start_offset fns1 + fn_offset)%nat.
  Proof.
    cbv [program_size]; induction fns1; intros.
    { rewrite ?app_nil_l in *. cbn [link_symbols' maybe_fold_left] in *.
      maybe_simpl. destruct_products.
      eauto using link_symbols'_no_overwrite, link_symbols_for_function_correct. }
    { rewrite <-?app_comm_cons in *. cbn [fold_left].
      repeat lazymatch goal with
             | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
                 eapply link_symbols'_inv in H
             | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
                 apply link_symbols_for_function_size in H; subst
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => subst; solve [eauto]                                 
             end. }
  Qed.

  Lemma link_symbols'_name :
    forall fns1 fns2 fn start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some (program_size start_offset fns1).
  Proof.
    intros.
    replace (program_size start_offset fns1)
      with (program_size start_offset fns1 + 0)%nat by lia.
    eapply link_symbols'_correct; eauto using get_label_offset_name.
  Qed.

  Lemma link_cinsn_correct syms i1 i2 : 
    link_cinsn syms i1 = Ok i2 ->
    cinsn_equiv syms i1 i2.
  Proof.
    cbv [link_cinsn cinsn_equiv]; intros.
    destruct_one_match; maybe_simpl; ssplit; auto;
      lazymatch goal with
      | H : map_err (map.get ?m ?k) _ = Ok _ |- _ =>
          destr (map.get m k); cbn [map_err] in H; maybe_simpl
      end; reflexivity.
  Qed.

  Lemma link_insn_correct syms i1 i2 : 
    link_insn syms i1 = Ok i2 ->
    insn_equiv syms i1 i2.
  Proof.
    cbv [link_insn insn_equiv]; intros.
    destruct_one_match; maybe_simpl; eauto using link_cinsn_correct.
  Qed.

  Lemma link_insns_correct :
    forall syms fn_insns prog,
      link_insns syms fn_insns = Ok prog ->
      forall (fn_offset : nat),
        (fn_offset < length fn_insns)%nat ->
        exists i1 i2,
          nth_error fn_insns fn_offset = Some i1
          /\ nth_error prog fn_offset = Some i2
          /\ insn_equiv syms i1 i2.
  Proof.
    induction fn_insns; intros; cbn [link_insns length] in *; maybe_simpl; [ lia | ].
    destr fn_offset; cbn [nth_error].
    { do 2 eexists; ssplit; try reflexivity; eauto using link_insn_correct. }
    { apply IHfn_insns; auto; lia. }
  Qed.

  Lemma linked_at_cons i prog syms fn offset :
    linked_at prog syms fn offset ->
    linked_at (i :: prog) syms fn (S offset).
  Proof.
    cbv [linked_at]; cbn [fst snd]. intro Hlink; intros.
    specialize (Hlink _ ltac:(eassumption)). destruct_products.
    eauto.
  Qed.

  Lemma link'_correct :
    forall start_prog fn prog syms offset,
      link' syms start_prog fn = Ok prog ->
      offset = length start_prog ->
      linked_at prog syms fn offset.
  Proof.
    cbv [link']; induction start_prog; intros; subst.
    { maybe_simpl. rewrite app_nil_l in *. cbn [length].
      cbv [linked_at]; intros.
      lazymatch goal with H : link_insns _ _ = _ |- _ =>
                            eapply link_insns_correct in H; eauto end.
      destruct_products. cbn [fst snd].
      rewrite fetch_fn_name. cbv [fetch]; cbn [fst snd].
      eauto. }
    { maybe_simpl. rewrite <-app_comm_cons. cbn [length].
      apply linked_at_cons. apply IHstart_prog; auto; maybe_simpl.
      reflexivity. }
  Qed.

  Lemma link'_no_unlink :
    forall fn1 fn2 syms offset start_prog prog,
      link' syms start_prog fn2 = Ok prog ->
      linked_at start_prog syms fn1 offset ->
      linked_at prog syms fn1 offset.
  Proof.
    cbv [link']; intros. maybe_simpl. cbv [linked_at]; intros.
    lazymatch goal with H : linked_at _ _ _ _ |- _ =>
                          specialize (H _ ltac:(eassumption))
    end.
    destruct_products. do 2 eexists; ssplit; eauto; [ ].
    cbv [fetch] in *; cbn [fst snd] in *.
    lazymatch goal with
    | H : nth_error ?l1 ?i = Some _ |- _ =>
        assert (i < length l1)%nat by eauto using List.nth_error_Some_bound_index
    end.
    rewrite nth_error_app1 by lia. auto.
  Qed.

  Lemma fold_link'_no_unlink :
    forall fns fn syms offset start_prog prog,
      maybe_fold_left (link' syms) fns start_prog = Ok prog ->
      linked_at start_prog syms fn offset ->
      linked_at prog syms fn offset.
  Proof.
    induction fns; cbn [maybe_fold_left]; intros; maybe_simpl;
      eauto using link'_no_unlink.
  Qed.

  Lemma link_insns_length :
    forall syms insns prog,
    link_insns syms insns = Ok prog ->
    length prog = length insns.
  Proof.
    induction insns; cbn [link_insns length]; intros; maybe_simpl; [ reflexivity | ].
    cbn [length]. rewrite IHinsns; eauto.
  Qed.

  Lemma link'_length syms start_prog fn prog:
    link' syms start_prog fn = Ok prog ->
    length prog = (length start_prog + length (snd fn))%nat.
  Proof.
    cbv [link']. destruct fn as [[fn_name fn_syms] fn_insns]. cbn [fst snd].
    intros; maybe_simpl. rewrite app_length.
    lazymatch goal with H : link_insns _ _ = _ |- _ => apply link_insns_length in H end.
    lia.
  Qed.

  Lemma link_correct'' :
    forall fns1 fn fns2 start_syms start_offset start_prog syms prog end_offset,
      maybe_fold_left (link' syms) (fns1 ++ fn :: fns2) start_prog = inl prog ->
      link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = inl (syms, end_offset) ->
      start_offset = length start_prog ->
      linked_at prog syms fn (program_size start_offset fns1).
  Proof.
    cbv [program_size]. induction fns1; intros; subst.
    { rewrite app_nil_l in *. cbn [maybe_fold_left fold_left fst snd] in *.
      maybe_simpl. eauto using link'_correct, fold_link'_no_unlink. }
    { rewrite <-?app_comm_cons in *. cbn [fold_left maybe_fold_left] in *.
      maybe_simpl.
      repeat lazymatch goal with
             | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
                 eapply link_symbols'_inv in H
             | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
                 apply link_symbols_for_function_size in H; subst
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => progress subst                           
             end.
      eapply IHfns1; eauto; [ ].
      cbv [otbn_function] in *; destruct_products; cbn [fst snd] in *.
      lazymatch goal with H : link' _ _ _ = _ |- _ => apply link'_length in H end.
      cbn [fst snd] in *. lia. }
  Qed.

  Lemma link_correct' fns1 fns2 fn prog syms :
      link (fns1 ++ fn :: fns2) = Ok prog ->
      link_symbols (fns1 ++ fn :: fns2) = Ok syms ->
      linked_at prog syms fn (program_size 0%nat fns1).
  Proof.
    cbv [link link_symbols]; intros. maybe_simpl.
    destruct_products; cbn [fst snd] in *.
    eauto using link_correct''.    
  Qed.

  Lemma link_correct :
    forall fns fn prog syms,
      (* If the function is in the input list of functions `fns`... *)
      In fn fns ->
      (* ...and `prog` is the result of a successful `link`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...then there exists an `offset` and an index `idx`... *)
      exists offset idx,
        (* ...such that `fn` is in the list at index `idx`...  *)
        nth_error fns idx = Some fn
        (* ...and `offset` is the size of the program before `fn`... *)
        /\ offset = program_size 0%nat (firstn idx fns)
        (* ...and `fn` is linked at `offset`. *)
        /\ linked_at prog syms fn offset.
  Proof.
    intros.
    lazymatch goal with H : In _ _ |- _ =>
                          apply in_split in H; destruct H as [fns1 [fns2 ?]]
    end.
    subst. eexists; exists (length fns1); ssplit; [ | reflexivity | ].
    { rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite List.firstn_app_l by lia. eauto using link_correct'. }
  Qed.

  Definition pcs_related (syms : symbols) (pc1 : string * nat) (pc2 : nat * nat) : Prop :=
    map.get syms (fst pc1) = Some (fst pc2) /\ snd pc1 = snd pc2.
  Definition loop_stack_entries_related (syms : symbols) (e1 : _ * nat) (e2 : _ * nat) : Prop :=
    pcs_related syms (fst e1) (fst e2) /\ snd e1 = snd e2.
  Definition states_related (syms : symbols)
    (st1 : otbn_state (label:=string)) (st2 : otbn_state (label:=nat)) : Prop :=
    match st1, st2 with
    | otbn_busy pc1 regs1 wregs1 flags1 dmem1 cstack1 lstack1,
      otbn_busy pc2 regs2 wregs2 flags2 dmem2 cstack2 lstack2 =>
        pcs_related syms pc1 pc2
        /\ regs1 = regs2
        /\ wregs1 = wregs2
        /\ flags1 = flags2
        /\ dmem1 = dmem2
        /\ Forall2 (pcs_related syms) cstack1 cstack2
        /\ Forall2 (loop_stack_entries_related syms) lstack1 lstack2
    | otbn_done pc1 dmem1, otbn_done pc2 dmem2 =>
        pcs_related syms pc1 pc2
        /\ dmem1 = dmem2
    | otbn_error pc1 errs1, otbn_error pc2 errs2 =>
        pcs_related syms pc1 pc2
        /\ errs1 = errs2
    | _, _ => False
    end.

  Lemma link_symbols_correct fns fn syms fn_offset dst n :
    link_symbols fns = inl syms ->
    nth_error fns n = Some fn ->
    get_label_offset fn dst = Some fn_offset ->
    map.get syms dst = Some (program_size 0 (firstn n fns) + fn_offset)%nat.
  Proof.
    cbv [link_symbols]. intros. maybe_simpl. destruct_products.
    repeat lazymatch goal with
           | H : nth_error _ _ = Some _ |- _ =>
               apply nth_error_split in H
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           end.
    subst. rewrite List.firstn_app_l by reflexivity. cbn [fst snd].
    eauto using link_symbols'_correct.
  Qed.

  Lemma link_fetch syms prog fns pc1 pc2 i1 :
    link fns = Ok prog ->
    link_symbols fns = Ok syms ->
    pcs_related syms pc1 pc2 ->
    fetch_ctx fns pc1 = Some i1 ->
    exists i2,
      fetch prog pc2 = Some i2
      /\ insn_equiv syms i1 i2.
  Proof.
    cbv [pcs_related]; intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : fetch_ctx _ _ = Some _ |- _ => apply fetch_ctx_Some in H
           end.
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H; subst
           | H : exists _, _ |- _ => destruct H
           | H : fetch_fn ?fn (fst (fst ?fn), _) = Some _ |- _ => rewrite fetch_fn_name in H
    
           | H : fetch_fn _ _ = Some _ |- _ => apply fetch_fn_Some in H
           | H : @nth_error insn _ ?n = Some _, H' : linked_at _ _ _ _ |- _ =>
               specialize (H' n ltac:(eauto using List.nth_error_Some_bound_index))
           end.

    lazymatch goal with
    | H : nth_error ?l ?i = Some ?x, H' : nth_error ?l ?i = Some ?y |- _ =>
        assert (x = y) by congruence; subst
    end.
 
    pose proof (link_symbols_correct
                  _ _ _ _ _ _
                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    lazymatch goal with
    | H : map.get ?m ?k = Some ?x, H' : map.get ?m ?k = Some ?y |- _ =>
        assert (x = y) by congruence; subst
    end.

    lazymatch goal with
    | H : fetch prog _ = Some ?i |- _ => exists i
    end.
    ssplit; [ | assumption .. ].
    destruct_products.
    cbv [fetch] in *. cbn [fst snd] in *. subst.
    lazymatch goal with
    | H : _ = Some ?x |- _ = Some ?x => rewrite <-H
    end.
    repeat (f_equal; try lia).
  Qed.

  (* simplify goals about pre- and post-link states that correspond *)
  Local Ltac related_states_hammer :=
    cbn [states_related] in *;
      repeat lazymatch goal with
        | H : False |- _ => contradiction H
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H; subst
        | H : forall st1' st2', _ st1' st2' -> _ st1' -> ?spec2 st2' |- ?spec2 _ =>
            eapply H; [ | eassumption ]
        | H : Forall2 _ (_ :: _) _ |- _ =>
            inversion H; clear H; subst; cbn [hd_error tl] in *
        | H : context [match ?x with _ => _ end] |- _ => destruct_one_match_hyp
        | |- context [match ?x with _ => _ end] => destruct_one_match
        | H : hd_error ?l = Some _ |- _ =>
            destruct l; cbn [hd_error tl] in *                                               
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | H : None = Some _ |- _ => exfalso; congruence
        | |- pcs_related _ _ _ =>
            progress cbv [advance_pc pcs_related] in *; cbn [fst snd]; ssplit; eauto
        | |- loop_stack_entries_related _ _ _ =>
            progress cbv [loop_stack_entries_related] in *; ssplit
        | |- states_related _ _ _ =>
            progress cbv [states_related]; try contradiction; ssplit; eauto
        | H: Forall2 _ ?l1 ?l2,
            H0 : (length ?l1 < ?n)%nat, H1 : (?n <= length ?l2)%nat |- _ =>
            pose proof (Forall2_length H); lia
        | |- Forall2 _ (_ :: _) (_ :: _) => constructor
        | |- read_gpr _ _ _ =>
            eapply read_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_wdr _ _ _ =>
            eapply read_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_flag _ _ _ =>
            eapply read_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_byte _ _ _ =>
            eapply load_byte_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_bytes _ _ _ _ =>
            eapply load_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_word _ _ _ =>
            eapply load_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_byte _ _ _ _ =>
            eapply store_byte_weaken; [ eassumption | ]; cbv beta; intros
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
        | |- apply_shift _ _ _ =>
            eapply apply_shift_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_flag _ _ _ _ =>
            eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- update_mlz _ _ _ _ =>
            eapply update_mlz_weaken; [ eassumption | ]; cbv beta; intros
        | |- exists _, _ =>
            eexists; ssplit; first [ eassumption
                                   | reflexivity
                                   | solve [related_states_hammer] ]
        | _ => first [ progress (cbv [call_stack_pop call_stack_push
                                        loop_start loop_end loop_stack_entries_related
                                        read_gpr_from_state next_pc
                                        set_pc update_state program_exit] in *;
                                 cbn [fst snd err option_bind proof_semantics] in *; subst )
                     | congruence
                     | solve [eauto] ]
        end.

  Lemma ctrl1_weaken syms i1 i2 st1 st2 spec1 spec2 :
    ctrl1 (label:=string) st1 i1 spec1 ->
    states_related syms st1 st2 ->
    cinsn_equiv syms i1 i2 ->
    (forall st1' st2', states_related syms st1' st2' -> spec1 st1' -> spec2 st2') ->
    ctrl1 (label:=nat) st2 i2 spec2.
  Proof.
    cbv [ctrl1 cinsn_equiv err option_bind proof_semantics]; intros.
    destruct st1, st2; related_states_hammer.
  Qed.

  (* prove that run1 on related states produces a related state *)
  Lemma link_run1 fns prog syms st1 st2 spec1 spec2 :
      link fns = Ok prog ->
      link_symbols fns = Ok syms ->
      states_related syms st1 st2 ->
      (forall st1' st2',
          states_related syms st1' st2' ->
          spec1 st1' ->
          spec2 st2') ->
      run1 (fetch:=fetch_ctx fns) st1 spec1 ->
      run1 (fetch:=fetch prog) st2 spec2.
  Proof.
    cbv [run1].
    destruct st1, st2; cbn [states_related]; try contradiction; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : fetch_ctx _ _ = Some _ |- _ => eapply link_fetch in H; [ | eassumption .. ]
        | H : forall st1' st2',
            states_related _ st1' st2' ->
              spec1 st1' ->
              spec2 st2' |- spec2 _ =>
            eapply H; eauto; cbv [states_related]; ssplit; solve [eauto]
        | _ => progress subst
        end; [ ].
    eexists; ssplit; [ eauto | ].
    cbv [insn_equiv] in *.
    destruct_one_match; destruct_one_match_hyp; subst; try contradiction; [ | ].
    { (* straightline case *)
      eapply strt1_weaken; [ eassumption | ].
      cbv beta; intros.
      related_states_hammer. }
    { (* ctrl1 case *)
      eapply ctrl1_weaken; try eassumption; [ ].
      related_states_hammer. ssplit; related_states_hammer. }
  Qed.

  Lemma link_eventually_run1 fns prog syms st1 st2 spec1 spec2 :
      link fns = Ok prog ->
      link_symbols fns = Ok syms ->
      (forall st1' st2',
          states_related syms st1' st2' ->
          spec1 st1' ->
          spec2 st2') ->
      states_related syms st1 st2 ->
      eventually (run1 (fetch:=fetch_ctx fns)) spec1 st1 ->
      eventually (run1 (fetch:=fetch prog)) spec2 st2.
  Proof.
    intros. generalize dependent st2.
    let H := lazymatch goal with H : eventually _ _ _ |- _ => H end in
    induction H; intros; [ solve [eauto using eventually_done] | ].    
    eapply eventually_step; [ | solve [eauto] ].
    eapply link_run1; eauto.      
  Qed.

  Lemma link_symbols_name fns1 fns2 fn name syms :
    link_symbols (fns1 ++ fn :: fns2) = Ok syms ->
    name = fst (fst fn) ->
    map.get syms name = Some (program_size 0%nat fns1).
  Proof.
    cbv [link_symbols]; maybe_simpl; intros; subst; [ | congruence ].
    destruct_products; cbn [fst snd] in *.
    lazymatch goal with H : inl _ = inl _ |- _ => inversion H; clear H; subst end.
    eauto using link_symbols'_name.
  Qed.

  (* Theorem that connects run1 with a ctx to run1 with a program *)
  Lemma link_exits' :
    forall fns prog syms start_fn start_name n start_pc regs wregs flags dmem spec err_spec,
      (* ...if `prog` is the result of a successful `link fns`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...and `start_fn` is in the list... *)
      nth_error fns n = Some start_fn ->
      (* ...and `start_pc` is the global offset... *)
      start_pc = program_size 0%nat (firstn n fns) ->
      (* ...and `start_name is the name of the starting function... *)
      start_name = fst (fst start_fn) ->
      (* ...and the pre-link version satisfies the spec... *)
      exits (fetch:=fetch_ctx fns) start_name regs wregs flags dmem [] [] spec err_spec ->
      (* ...the program satisfies the spec. *)
      exits (fetch:=fetch prog) start_pc regs wregs flags dmem [] [] spec err_spec.
  Proof.
    cbv [exits]; intros.
    assert (In start_fn fns) by (eauto using nth_error_In).
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : nth_error _ _ = Some _ |- _ => apply nth_error_split in H
           | _ => progress subst
           end.
    eapply link_eventually_run1; eauto; [ | ].
    { cbv beta; intros.
      cbv [states_related] in *.
      related_states_hammer. }
    { cbv beta; intros.
      cbv [states_related]; ssplit; related_states_hammer.
      eapply link_symbols_name; [ | reflexivity .. ].
      rewrite List.firstn_app_l by lia.
      eauto. }
  Qed.

  (* like `find` except returns the index of the match *)
  Definition find_index {A} (f : A -> bool) (l : list A) : option nat :=    
    find (fun idx =>
            match nth_error l idx with
            | Some a => f a
            | None => false
            end)
      (seq 0 (length l)).

  Definition find_global_offset (fns : list otbn_function) (name : string) : option nat :=
    match find_index (fun fn => String.eqb name (fst (fst fn))) fns with
    | Some idx => Some (program_size 0%nat (firstn idx fns))
    | None => None
    end.

  Lemma find_app :
    forall {A} (f : A -> bool) l1 l2,
      find f (l1 ++ l2) = match find f l1 with
                          | Some x => Some x
                          | None => find f l2
                          end.
  Proof.
    induction l1 as [|a ?]; intros; [ reflexivity | ].
    rewrite <-app_comm_cons. cbn [find].
    destruct_one_match; eauto.
  Qed.

  Lemma find_map :
    forall {A B} (f : B -> bool) (g : A -> B) l,
      find f (List.map g l) = option_map g (find (fun a => f (g a)) l).
  Proof.
    cbv [option_map].
    induction l; cbn [find List.map]; intros; [ congruence | ].
    destruct_one_match_hyp; destruct_one_match;
      repeat lazymatch goal with
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | _ => first [ solve [eauto] | congruence ]
        end.
  Qed.

  Lemma find_map_inv :
    forall {A B} (f : B -> bool) (g : A -> B) l b,
      find f (List.map g l) = Some b ->
      exists a,
        find (fun a => f (g a)) l = Some a
        /\ g a = b.
  Proof.
    induction l; cbn [find List.map]; intros; [ congruence | ].
    destruct_one_match_hyp;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | H : find _ (List.map _ _) = Some _ |- _ => apply IHl in H
        | _ => solve [eauto]
        end.
  Qed.

  Lemma program_size_add :
    forall fns start,
      fold_left
        (fun offset (fn : otbn_function) => (offset + length (snd fn))%nat)
        fns start = (fold_left
                       (fun offset (fn : otbn_function) => (offset + length (snd fn))%nat)
                       fns 0 + start)%nat.
  Proof.
    induction fns; cbn [fold_left]; intros; [ lia | ].
    rewrite !(IHfns (_ + _)%nat). lia.
  Qed.

  Lemma program_size_equiv :
    forall fns1 fns2 fns3 fns4 a b start,
      program_size start fns1 = program_size start fns2 ->
      fns1 ++ a :: fns3 = fns2 ++ b :: fns4 ->
      (0 < length (snd a))%nat ->
      (0 < length (snd b))%nat ->
      a = b.
  Proof.
    cbv [program_size].
    induction fns1; destruct fns2; intros *; rewrite ?app_nil_l, <-?app_comm_cons;
      cbn [app fold_left]; intros; subst;
      repeat lazymatch goal with
        | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
        | H : ?start = fold_left _ _ (?start + _)%nat |- _ =>
            rewrite program_size_add in H; lia
        | H : fold_left _ _ (?start + _)%nat = ?start |- _ =>
            rewrite program_size_add in H; lia
        | |- ?x = ?x => reflexivity
        | _ => solve [eauto]
        end.
  Qed.

  Lemma link_symbols'_app :
    forall fns1 fns2 start_syms start_offset end_offset syms,
      link_symbols' start_syms start_offset (fns1 ++ fns2) = Ok (syms, end_offset) ->
      exists syms1 end_offset1,
        link_symbols' start_syms start_offset fns1 = Ok (syms1, end_offset1)
        /\ link_symbols' syms1 end_offset1 fns2 = Ok (syms, end_offset).
  Proof.
    induction fns1; cbn [app]; intros; rewrite ?app_nil_l, <-?app_comm_cons in *;
      [ do 2 eexists; ssplit; [ reflexivity | eauto ] | ].
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               apply link_symbols'_inv in H
           | H : link_symbols' _ _ (_ ++ _) = Ok _ |- _ =>
               apply IHfns1 in H
           | _ => progress subst
           end.    
    erewrite link_symbols'_step by eauto.
    eauto.
  Qed.

  Lemma link_symbols'_no_dup' :
    forall fns start_syms start_offset end_offset syms fn1 fn2 n1 n2,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      nth_error fns n1 = Some fn1 ->
      nth_error fns n2 = Some fn2 ->
      (n1 < n2)%nat ->
      fst (fst fn1) <> fst (fst fn2).
  Proof.
    intros. intro; subst.
    repeat lazymatch goal with 
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : nth_error (_ ++ _) _ = _ |- _ => rewrite nth_error_app2 in H by lia
           | H : nth_error (_ :: _) _ = Some _ |- _ =>
               rewrite nth_error_cons in H; destruct_one_match_hyp; [ lia | ]
           | H : nth_error _ n1 = Some _ |- _ =>
               apply List.nth_error_split in H
           | H : nth_error _ ?n = Some _, H' : _ = S ?n |- _ =>
               apply List.nth_error_split in H
           | H : link_symbols' _ _ (_ ++ _) = Ok _ |- _ =>
               apply link_symbols'_app in H
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               apply link_symbols'_inv in H
           | _ => progress (cbn [fst snd] in *; subst)
           end.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : link_symbols_for_function _ fn1 = _ |- _ =>
               apply link_symbols_for_function_name in H
           | H : link_symbols_for_function (?syms, ?off) fn2 = _,
               H' : map.get ?syms _ = Some _ |- _ =>
               eapply link_symbols_for_function_name_fail with (fn:=fn2) (start_offset:=off) in H';
               [ | solve [eauto] ]
           | H : link_symbols' ?syms _ _ = _, H' : map.get ?syms _ = Some _ |- _ =>
               eapply link_symbols'_no_overwrite in H; [ | solve [eauto] .. ]
           | _ => progress (cbn [fst snd] in *; subst)
           end.
    congruence.
  Qed.

  Lemma link_symbols'_no_dup :
    forall fns start_syms start_offset end_offset syms fn1 fn2,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      In fn1 fns ->
      In fn2 fns ->
      fst (fst fn1) = fst (fst fn2) ->
      fn1 = fn2.      
  Proof.
    intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : In _ _ |- _ => apply In_nth_error in H
           end.
    lazymatch goal with
    | H1 : nth_error fns ?n1 = Some fn1,
        H2 : nth_error fns ?n2 = Some fn2 |- _ =>
        destr (n1 <? n2)%nat;
        [ | destr (n2 <? n1)%nat;
            [ | assert (n1 = n2) by lia; subst ] ]
    end; lazymatch goal with
         | H : (_ < _)%nat |- _ => eapply link_symbols'_no_dup' in H; eauto; congruence
         | _ => congruence
         end.
  Qed.

  Lemma link_symbols_no_dup :
    forall fns syms fn1 fn2,
      link_symbols fns = Ok syms ->
      In fn1 fns ->
      In fn2 fns ->
      fst (fst fn1) = fst (fst fn2) ->
      fn1 = fn2.      
  Proof.
    cbv [link_symbols].
    intros. maybe_simpl. destruct_products.
    eapply link_symbols'_no_dup; eauto.    
  Qed.

  Lemma find_ext {A} (f g : A -> bool) l (Hext : forall a, f a = g a) :
    find f l = find g l.
  Proof.
    induction l; cbn [find]; intros; [ reflexivity | ].
    rewrite Hext, IHl; reflexivity.
  Qed.

  Lemma find_index_cons {A} (f : A -> bool) l a :
      find_index f (a :: l) = if f a then Some 0%nat else option_map S (find_index f l).
  Proof.
    cbv [find_index]. cbn [length].
    rewrite <-cons_seq, <-seq_shift.
    cbn [find nth_error]. destruct_one_match; [ reflexivity | ].    
    rewrite find_map; reflexivity.
  Qed.

  Lemma find_index_Some :
    forall {A} (f : A -> bool) l i,
      find_index f l = Some i ->
      exists a,
        nth_error l i = Some a
        /\ f a = true.
  Proof.
    induction l; intros.
    { cbn [find_index length nth_error seq find] in *. congruence. }
    { rewrite find_index_cons in *. cbv [option_map] in *.
      repeat lazymatch goal with
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | H : None = Some _ |- _ => congruence
             | H : context [match ?x with _ => _ end] |- _ => destruct_one_match_hyp
             | _ => first [ progress (cbn [nth_error] in *; subst)
                          | solve [eauto] ]
             end. }    
  Qed.

  Lemma find_global_offset_correct' :
    forall fns syms fn name offset,
      In fn fns ->
      link_symbols fns = Ok syms ->
      find_global_offset fns name = Some offset ->
      name = fst (fst fn) ->
      exists n,
        nth_error fns n = Some fn
        /\ offset = program_size 0%nat (firstn n fns).
  Proof.
    cbv [find_global_offset]. intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           | H : None = Some _ |- _ => congruence
           | H : find_index _ _ = Some _ |- _ => apply find_index_Some in H
           | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
           | H : nth_error _ _ = Some ?fn, H' : fst (fst _) = fst (fst ?fn) |- _ =>
               eapply link_symbols_no_dup in H'; eauto using nth_error_In; subst; eauto
           | _ => first [ progress subst | destruct_one_match_hyp ]
           end.
  Qed.

  Lemma find_global_offset_correct :
    forall fns syms name offset,
      link_symbols fns = Ok syms ->
      find_global_offset fns name = Some offset ->
      exists fn n,
        nth_error fns n = Some fn
        /\ name = fst (fst fn)
        /\ In fn fns
        /\ offset = program_size 0%nat (firstn n fns).
  Proof.
    cbv [find_global_offset]. intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           | H : None = Some _ |- _ => congruence
           | H : find_index _ _ = Some _ |- _ => apply find_index_Some in H
           | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
           | _ => first [ progress subst | destruct_one_match_hyp ]
           end.
    do 2 eexists; ssplit; eauto using nth_error_In.    
  Qed.

  (* Theorem that connects run1 with a ctx to run1 with a program *)
  Lemma link_exits :
    forall fns prog syms start_name start_pc regs wregs flags dmem spec err_spec,
      (* ...if `prog` is the result of a successful `link fns`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...and `start_pc` is the global offset of `start_name`... *)
      find_global_offset fns start_name = Some start_pc ->
      (* ...and the pre-link version satisfies the spec... *)
      exits (fetch:=fetch_ctx fns) start_name regs wregs flags dmem [] [] spec err_spec ->
      (* ...the program satisfies the spec. *)
      exits (fetch:=fetch prog) start_pc regs wregs flags dmem [] [] spec err_spec.
  Proof.
    cbv [exits]; intros.
    lazymatch goal with H : find_global_offset _ _ = Some _ |- _ =>
                          eapply find_global_offset_correct in H; [ | solve [eauto] ] end.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | _ => progress subst
           end.
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end.
    eapply link_eventually_run1; eauto; [ | ].
    { cbv beta; intros.
      cbv [states_related] in *.
      related_states_hammer. }
    { cbv beta; intros.
      cbv [states_related]; ssplit; related_states_hammer.
      repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : nth_error _ _ = Some ?fn |- map.get syms (fst (fst ?fn)) = _ =>
                 apply nth_error_split in H
             | _ => progress subst
             end.
      erewrite link_symbols_name by eauto.
      rewrite List.firstn_app_l by lia.
      reflexivity. }
  Qed.
End __.
