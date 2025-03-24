Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.SortedListString.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import Otbn.ISA.ISA.
Require Import Otbn.ISA.Labels.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Util.Maybe.
Require Import Otbn.ISA.ToString.
Require Coq.Strings.HexString.
Import ListNotations.
Import MaybeNotations.
Import ISA.Coercions.
Local Open Scope Z_scope.

(*** Small fault-modelling example for a live HACS session 2025-03-24

The code examples (`hardened_word_cmp` and `hardened_array_cmp`) are simplified snippets loosely based on a fault-hardened equality check from OpenTitan:
https://github.com/lowRISC/opentitan/blob/b8865df6b779375e8bc0119ff80cec828928ea73/sw/device/silicon_creator/lib/sigverify/ecdsa_p256_verify.c#L96

Readers may be interested to know that the functional correctness of the full equality check was also verified in Rocq:
https://gist.github.com/jadephilipoom/b5feae0bc1b229715a4b9ac06a15e96c

***)

Section Specs.
  Context {word32 : word.word 32} {word256 : word.word 256}.
  Context {label : Type} {label_params : label_parameters label}.
  Context {regfile : map.map reg word32}
    {wregfile : map.map wreg word256}
    {flagfile : map.map flag bool}
    {mem : map.map word32 byte}
    {fetch : label * nat -> option (insn (label:=label))}.

  (* define the type of a fault model in omnisemantics style *)
  Definition fault_model : Type :=
    (otbn_state (label:=label) * nat) ->
    ((otbn_state (label:=label) * nat) -> Prop) -> Prop.

  (* very basic fault model that says one instruction can be skipped
     at any point, up to a certain bound *)
  Definition skip_insn_fault_model (max : nat) : fault_model :=
    fun '(state, count) post =>
      if (count <? max)%nat
      then
        match state with
        | otbn_busy pc regs wregs flags dmem cstack lstack =>
            (* postcondition must hold BOTH if we skip the next instruction and if we don't *)
            post (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack, (count + 1)%nat)
            /\ post (otbn_busy pc regs wregs flags dmem cstack lstack, count)
        | st =>
            (* no program running *)
            post (st, count)
        end            
      else
        (* no more faults *)
        post (state, count).

  (* "run 1 cycle" function that incorporates a customizable fault model *)
  Definition fault1
    (fault_step : fault_model)
    (state_and_score : otbn_state * nat)
    (post : otbn_state * nat -> Prop) : Prop :=
    let st := fst state_and_score in
    let sc := snd state_and_score in
    after1 (fetch:=fetch) (label:=label) st
      (fun st' => fault_step (st', sc) post).
End Specs.

Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics.
Require Import Otbn.Lib.Bignum.
Require Import Otbn.Semantics.Clobbers.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.Semantics.Properties.
Require Import Otbn.Semantics.Tactics.StraightlineStep.
Require Import Otbn.Util.Tactics.Mapsimpl.
Require Import Otbn.Util.Tactics.SubstLets.
Require Import Otbn.Util.Tactics.Zsimplify.

(* test programs *)
Section Defs.
  Import ISA.Notations.
  
  (* x13: lhs value to compare
     x14: rhs value to compare
     x10, x11: OK shares in memory
     x6: result

     precomputation: shares[0] ^ shares[1] = high-HW OK value

     pseudocode:
        x = lhs ^ shares[0]
        y = rhs ^ shares[1]
        return x ^ y
   *)
  Definition hardened_word_cmp_fn : otbn_function :=
    ("hardened_word_cmp"%string,
      map.empty,
      [[ nop
         ; xor x6, x13, x10
         ; xor x12, x14, x11
         ; xor x6, x6, x12
         ; ret
         ; unimp ]]%otbn).

  (* x2: holds the number of limbs (n)
     x3: points to the lhs in memory
     x4: points to the rhs in memory
     x5: points to the shares in memory
     x6: result

     precomputation: shares[0] ^ .. ^ shares[n-1] = high-HW OK value

     pseudocode:
        result = 0
        for i in range(n):
            t = lhs[i] ^ shares[i]
            t ^= rhs[i]
            res ^= t
        return result
   *)
  Definition hardened_array_cmp_fn : otbn_function :=
    ("hardened_array_cmp"%string,
      map.empty,
      [[ addi x6, x0, 0
         ; loop x2
         ; lw x13, 0(x3)
         ; lw x15, 0(x5)
         ; xor x13, x13, x15
         ; lw x14, 0(x4)
         ; xor x13, x13, x14
         ; xor x6, x6, x13
         ; addi x3, x3, 4
         ; addi x4, x4, 4
         ; loopend(addi x5, x5, 4)
         ; ret ]]%otbn).
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

  (* x13: lhs value to compare
     x14: rhs value to compare
     x10, x11: OK shares in memory
     x6: result

     precomputation: shares[0] ^ shares[1] = high-HW OK value

     pseudocode:
        x = lhs ^ shares[0]
        y = rhs ^ shares[1]
        return x ^ y
   *)
  Lemma hardened_word_cmp_correct :
    forall regs wregs flags dmem cstack lstack
           lhs rhs share0 share1 x12_old x6_old,
      (* initial register values *)
      map.get regs (gpreg x13) = Some lhs ->
      map.get regs (gpreg x14) = Some rhs ->
      map.get regs (gpreg x10) = Some share0 ->
      map.get regs (gpreg x11) = Some share1 ->
      (* need residual values x12, x6 in case the writes are faulted;
         no guarantees except not equal to *specific* bad values *)
      (* alternate phrasing: put in the postcondition that if the
         result is OK and lhs <> rhs, it means there was a fault and one
         of the registers had the bad value *)
      map.get regs (gpreg x12) = Some x12_old ->
      x12_old <> word.xor lhs share1 ->
      map.get regs (gpreg x6) = Some x6_old ->
      x6_old <> word.xor rhs share0 ->
      (* function specification *)
      forall ret_pc,
      hd_error cstack = Some ret_pc ->
      eventually
        (* use a fault model that skips at most 1 instruction *)
        (fault1 (skip_insn_fault_model 1) (fetch:=fetch_ctx [hardened_word_cmp_fn]))
        (fun '(st, count) =>
           match st with
           | otbn_busy pc regs' wregs' flags' dmem' cstack' lstack' =>
               pc = ret_pc
               (* the result is equal to the hardened OK value only if lhs = rhs *)
               /\ (exists result,
                      map.get regs' (gpreg x6) = Some result
                      (* result being the OK value always implies lhs = rhs, even in the presence of faults *)
                      /\ (result = word.xor share0 share1 -> lhs = rhs)
                      (* if there were no faults, then lhs = rhs implies the result is OK*)
                      /\ (count = 0%nat -> lhs = rhs -> result = word.xor share0 share1))
               (* memory was not changed *)
               /\ dmem' = dmem
               (* flags were not changed *)
               /\ clobbers [] flags flags'
               (* wide registers were not changed *)
               /\ clobbers [] wregs wregs'
               (* certain small registers WERE changed *)
               /\ clobbers [gpreg x6; gpreg x12] regs regs'
               (* call stack has been popped once *)
               /\ cstack' = tl cstack
               (* loop stack is unchanged *)
               /\ lstack' = lstack
           | otbn_error pc errs =>
               (* if we end up in an error state, a fault must have
                  occurred (e.g. ret was skipped) *)
               (count > 0)%nat
           | _ => False
           end)
        (otbn_busy ("hardened_word_cmp"%string, 0%nat) regs wregs flags dmem cstack lstack, 0%nat).
  Proof.
    cbv [hardened_word_cmp_fn returns]. intros; subst.
    destruct cstack as [|p ?]; cbn [hd_error] in *; [ congruence | ].
    assert (p = ret_pc) by congruence; subst p.
    track_registers_init.

    (* step through nop *)
    intros; subst; eapply eventually_step_cps.
    cbv [fault1]. cbn [fst snd].
    simplify_side_condition.
    cbv [skip_insn_fault_model]. destruct_one_match; try lia; [ ].
    split.
    { (* first case: fault happened! *)
      simplify_side_condition.
      track_registers_update.

      (* step through second xor *)
      eapply eventually_step_cps. simplify_side_condition.
      destruct_one_match; try lia; [ ].
      track_registers_update.

      (* step through third xor *)
      eapply eventually_step_cps. simplify_side_condition.
      destruct_one_match; try lia; [ ].
      track_registers_update.

      (* step through return *)
      eapply eventually_step_cps. simplify_side_condition.
      destruct_one_match; try lia; [ ].
      track_registers_update.

      (* prove that postcondition now holds *)
      eapply eventually_done.
      ssplit; try reflexivity; try solve_clobbers; [ ].
      eexists; ssplit; [ eassumption | | congruence ].
      (* OK value always implies lhs = rhs *)
      subst_lets.
      intros. exfalso.
      assert (x6_old = word.xor rhs share0); [ | congruence ].
      (* algebraic properties of xor, less instructive *)
      admit. }

    (* second case: no fault after first xor, continue *)
    (* TODO: continue this proof *)
  Abort.

  (*
some precomputed concrete values in case we need them:

  Definition hardened_ok : Z := 0xde9da7dd.
  (* sums to hardened_ok when combined via xor *)
  Definition hardened_ok_shares :=
    [ 0xe4e708fc;
      0xeca55856;
      0x659d5570;
      0x9f4f6f58;
      0x5f014e0d;
      0x910c9a5d;
      0xa686b5de;
      0x57a97319;
      0x96351061;
      0x851acfa9 ].
   *)

  Definition xor_sum (shares : list word32) : word32 :=
    fold_left word.xor shares (word.of_Z 0).

  Lemma hardened_array_cmp_correct :
    forall regs wregs flags dmem cstack lstack
           n lhs rhs shares ptr_lhs ptr_rhs ptr_shares Rlhs Rrhs Rshares,
      (* initial register values *)
      map.get regs (gpreg x2) = Some (word.of_Z (Z.of_nat n)) ->
      map.get regs (gpreg x3) = Some ptr_lhs ->
      map.get regs (gpreg x4) = Some ptr_rhs ->
      map.get regs (gpreg x5) = Some ptr_shares ->
      (* all lists have length n *)
      length lhs = n ->
      length rhs = n ->
      length shares = n ->
      (* separation-logic statements about values in memory (since
         there are no writes, it's actually OK if these overlap) *)
      (bignum_at (width:=32) ptr_lhs lhs * Rlhs)%sep dmem ->
      (bignum_at ptr_rhs rhs * Rrhs)%sep dmem ->
      (bignum_at ptr_shares shares * Rshares)%sep dmem ->
      (* function specification *)
      forall ret_pc,
      hd_error cstack = Some ret_pc ->
      eventually
        (after1 (fetch:=fetch_ctx [hardened_array_cmp_fn]))
        (fun st =>
           match st with
           | otbn_busy pc regs' wregs' flags' dmem' cstack' lstack' =>
               pc = ret_pc
               (* the result is equal to the hardened OK value only if lhs = rhs *)
               /\ (exists result,
                      map.get regs' (gpreg x6) = Some result
                      /\ (result = xor_sum shares <-> lhs = rhs))
               (* memory was not changed *)
               /\ dmem' = dmem
               (* flags were not changed *)
               /\ clobbers [] flags flags'
               (* wide registers were not changed *)
               /\ clobbers [] wregs wregs'
               (* certain small registers WERE changed *)
               /\ clobbers
                    [gpreg x3; gpreg x4; gpreg x5; gpreg x6; gpreg x13; gpreg x14; gpreg x15]
                    regs regs'
               (* call stack has been popped once *)
               /\ cstack' = tl cstack
               (* loop stack is unchanged *)
               /\ lstack' = lstack
           | _ => False
           end)
        (otbn_busy ("hardened_array_cmp"%string, 0%nat) regs wregs flags dmem cstack lstack).          
  Proof.
    cbv [hardened_array_cmp_fn returns]. intros; subst.
    straightline_step.
    print_next_insn.

    (* loop; use loop invariant lemma *)
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' wregs' flags' dmem' =>
           map.get regs (gpreg x3) = Some (word.add ptr_lhs (word.of_Z (4*Z.of_nat i)))
           /\ map.get regs (gpreg x4) = Some (word.add ptr_rhs (word.of_Z (4*Z.of_nat i)))
           /\ map.get regs (gpreg x5) = Some (word.add ptr_shares (word.of_Z (4*Z.of_nat i)))
           /\ (exists result,
                  map.get regs' (gpreg x6) = Some result
                  /\ (result = xor_sum (firstn i shares) <-> firstn i lhs = firstn i rhs))
           /\ dmem' = dmem
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
           /\ clobbers
                [gpreg x3; gpreg x4; gpreg x5; gpreg x6; gpreg x13; gpreg x14; gpreg x15]
                regs regs').
    (* TODO: loop proof *)
    
  Abort.
End Proofs.
