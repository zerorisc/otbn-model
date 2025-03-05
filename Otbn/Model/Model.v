Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import coqutil.Z.ZLib.
Require Coq.Strings.HexString.
Import ListNotations.
Local Open Scope Z_scope.

(*** Model of OTBN. ***)

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

Module Test.

  (* Test program : add two values from memory using pointers

     add_mem:
       lw   x2, 0(x12)
       lw   x3, 0(x13)
       add  x5, x2, x3
       sw   x5, 0(x12)
       ret
   *)
  Definition add_mem_fn : otbn_function :=
    ("add_mem",
      map.empty,
      [ (Lw x2 x12 0 : insn);
        (Lw x3 x13 0 : insn);
        (Add x5 x2 x3 : insn);
        (Sw x12 x5 0 : insn) ;
        (Ret : insn)])%string.


  (* Test program: add two bignums

     bignum_add:
       bn.add w5, w2, w3
       ret
  *)
  Definition bignum_add_fn : otbn_function :=
    ("bignum_add"%string,
      map.empty,
      [(Bn_add w5 w2 w3 0 FG0: insn);
       (Ret : insn)]).

  
  (* Test program : multiply small number by big number

     bignum_mul:
       bn.xor w2, w2, w2
       beq    x4, x0, _bignum_mul_end
       loop   x4, 2
         jal      x1, bignum_add
         bn.addi  w2, w5, 0
       _bignum_mul_end:
       ret
   *)
  Definition bignum_mul_fn : otbn_function :=
    Eval cbn [List.app length] in (
        let syms := map.empty in
        let body : list insn :=
          [ (Bn_xor w2 w2 w2 0 FG0 : insn);
            (Beq x4 x0 "_bignum_mul_end" : insn);
            (Loop x4 : insn);
            (Jal x1 "bignum_add" : insn);
            (Bn_addi w2 w5 0 FG0 : insn);
            (LoopEnd : insn)] in
        let syms := map.put syms "_bignum_mul_end" (length body) in
        let body := (body ++  [(Ret : insn)])%list in
        ("bignum_mul", syms, body))%string.

  (* Test program : add two bignums from memory using pointers

     bignum_add_mem:
       li       x2, 2
       li       x3, 3
       bn.lid   x2, 0(x12)
       bn.lid   x3, 0(x13)
       bn,add   w2, w2, w3
       bn.sid   x2, 0(x12)
       ret
   *)
  Definition bignum_add_mem_fn : otbn_function :=
    ("bignum_add_mem",
      map.empty,
      [ (Addi x2 x0 2 : insn);
        (Addi x3 x0 3 : insn);
        (Bn_lid x2 false x12 false  0 : insn);
        (Bn_lid x3 false x13 false  0 : insn);
        (Bn_add w2 w2 w3 0 FG0 : insn);
        (Bn_sid x2 false x12 false  0 : insn);
        (Ret : insn)])%string.

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
    track_registers_init.

    repeat straightline_step.

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    ecancel_assumption.
  Qed.

  Lemma bignum_add_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get wregs (wdreg w2) = Some a ->
      map.get wregs (wdreg w3) = Some b ->
      returns
        (fetch:=fetch_ctx [bignum_add_fn])
        "bignum_add"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w5) = Some (word.add a b)
           /\ map.get flags' (flagC FG0) = Some (2^256 <=? word.unsigned a + word.unsigned b)
           /\ dmem' = dmem
           /\ clobbers [flagC FG0; flagM FG0; flagZ FG0; flagL FG0] flags flags'
           /\ clobbers [wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [add_fn returns]. intros; subst.
    track_registers_init.
    
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
  
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | | | | ].
    { solve_map. }
    { solve_map. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
  Qed.

  Lemma word_xor_same {width : Z} {word : word width} {word_ok : word.ok word} :
    forall x : word, word.xor x x = word.of_Z 0.
  Proof.
    intros. apply word.unsigned_inj.
    rewrite word.unsigned_xor, word.unsigned_of_Z_0.
    rewrite Z.lxor_nilpotent. pose proof word.modulus_pos.
    apply Z.mod_0_l. lia.
  Qed.

  Lemma bignum_mul_correct :
    forall regs wregs flags dmem cstack lstack (a v : word256) (b: word32),
      map.get wregs (wdreg w2) = Some v -> (* ignored, xored *)
      map.get wregs (wdreg w3) = Some a ->
      map.get regs (gpreg x4) = Some b ->
      (length cstack < 8)%nat ->
      (length lstack < 8)%nat ->
      returns
        (fetch:=fetch_ctx [bignum_mul_fn; bignum_add_fn])
        "bignum_mul"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w2) = Some (word.mul a (word.of_Z (word.unsigned b)))
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [bignum_mul_fn returns]. intros; subst.
    repeat straightline_step.

    (* branch; use branch helper lemma *)
    eapply eventually_beq.
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { simplify_side_condition; reflexivity. }
    { (* case: b = 0, exit early *)
      intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
      rewrite word.unsigned_of_Z_0. rewrite word.mul_0_r.
      ssplit; try reflexivity; [ | | ].
      { (* result value *)
        solve_map; subst_lets.
        rewrite word_xor_same. reflexivity. }
      { eapply clobbers_incl; eauto.
        cbv [incl In]; tauto. }
      { assumption. } }
    (* case: b <> 0, proceed *)
    intros; subst.

    pose proof (word.unsigned_range b).
    assert (0 < word.unsigned b).
    { lazymatch goal with H : b <> word.of_Z 0 |- _ =>
                            apply word.unsigned_inj' in H end.
      rewrite word.unsigned_of_Z_0 in *.
      lia. }
 
    (* loop; use loop invariant lemma *)
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w2) = Some (word.mul a (word.sub (word.of_Z (word.unsigned b)) (word.of_Z (Z.of_nat i))))
           /\ map.get wregs' (wdreg w3) = Some a
           /\ map.get regs' (gpreg x4) = Some b
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; simplify_side_condition; zsimplify; try reflexivity.
      { (* accumulator value *)
        subst_lets. apply f_equal. rewrite word_xor_same.
        ring. }
      { (* clobbered registers *)
        solve_clobbers. } }
    { (* invariant step; proceed through loop and prove invariant still holds *)
      intros; subst. repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.

      (* helper assertion that mul and add don't share symbols *)
      assert (function_symbols_disjoint bignum_add_fn bignum_mul_fn).
      { cbv [function_symbols_disjoint]; cbn [bignum_add_fn bignum_mul_fn fst snd].
        ssplit; solve_map; try congruence; [ ].
        cbv [map.disjoint]; intros *. rewrite map.get_empty; congruence. }

      (* jump to "bignum_add" function *)
      eapply eventually_jump.
      { reflexivity. }
      { lia. }
      { apply bignum_add_correct; eauto. }
      { intros.
        rewrite fetch_ctx_weaken_cons_ne; [ eassumption | ].
        eapply fetch_fn_disjoint; eauto; [ ].
        eapply fetch_ctx_singleton_iff; eauto. }

      (* post-jump; continue *)
      cbv beta. intros; subst.
      repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             end.
      track_registers_combine.

      repeat straightline_step.      

      (* end of loop; use loop-end helper lemma *)
      eapply eventually_loop_end; [ reflexivity .. | ].
      destruct_one_match.
      { (* case: i = 0, loop ends *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ ].
        simplify_side_condition; subst_lets; zsimplify.
        apply f_equal. ring. }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ ].
        simplify_side_condition. subst_lets; zsimplify.
        apply f_equal.
        replace (word.of_Z (width:=256) (Z.of_nat (S (S i))))
          with (word.add (width:=256) (word.of_Z (Z.of_nat (S i))) (word.of_Z 1));
          [ ring | ].
        apply word.unsigned_inj.
        rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
        cbv [word.wrap]. rewrite Z.mod_small by lia. lia. } }
 
    (* invariant implies postcondition (i.e. post-loop code) *)
    zsimplify. rewrite word.sub_0_r. intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           end.
    simplify_side_condition.
    repeat straightline_step.
    intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; eauto.
  Qed.

  Lemma bignum_add_mem_correct :
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
        (fetch:=fetch_ctx [bignum_add_mem_fn])
        "bignum_add_mem"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           (word_at pa (word.add a b) * Ra)%sep dmem'
           /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags'
           /\ clobbers [wdreg w2; wdreg w3] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x3] regs regs').
  Proof.
    cbv [bignum_add_mem_fn returns]. intros; subst.
    track_registers_init.
    
    repeat straightline_step.

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | solve_clobbers .. ].
    ecancel_assumption.
  Qed.

End __.
End Test.

(* Next: add mulqacc *)
(* Next: prove sha512 copy *)
(* Next: try to add more realistic error conditions for e.g. loop errors *)
(* Next: add notations back *)
(* Next: provable multiplication blocks *)
(* Next: add more insns needed for 25519 mul *)
(* Next: prove 25519 mul *)
(* Next: prove bignum op with var #regs (e.g. mul) *)
