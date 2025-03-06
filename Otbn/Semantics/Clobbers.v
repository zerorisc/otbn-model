Require Import Coq.Lists.List.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Util.Map.
Require Import Otbn.Semantics.Semantics.
Require Import Otbn.ISA.RegisterEquality.
Import ListNotations.

(*** Lemmas and tactics that help track which registers/flags are overwritten. ***)

(*
Register-tracking tl;dr:
- call `track_registers_init` at the start of your proof
- call `track_registers_update` after processing each instruction
- call `track_registers_combine` after returning from a jump or loop with its own spec
- call `solve_clobbers` at the end of the proof for goals of the form `clobbers _ _ _`

This way, you should always have a hypothesis in scope that looks something like:

H : clobbers [gpreg x2] regs regs6
=======
<some goal with `regs6` in it>

...where `regs` is the starting state of the registers.

You should have similar hypotheses for flags and wide registers.
*)

Section __.
  Context {K V} {map : map.map K V} {map_ok : map.ok map}.
  Context {key_eqb : K -> K -> bool}
    {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

  Definition clobbers (l : list K) (m m' : map.rep (map:=map)) : Prop :=
    map.only_differ m (PropSet.of_list l) m'.

  Lemma clobbers_step_in l k v r1 r2 :
    clobbers l r1 r2 ->
    In k l ->
    clobbers l r1 (map.put r2 k v).
  Proof.
    cbv [clobbers PropSet.of_list]; intros.
    intro k'; cbv [map.only_differ PropSet.elem_of] in *.
    lazymatch goal with H : forall k : K, _ |- _ => specialize (H k') end.
    destr (key_eqb k k'); rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
    all:tauto.
  Qed.

  Lemma clobbers_step l k v r1 r2 :
    clobbers l r1 r2 ->
    clobbers (k :: l) r1 (map.put r2 k v).
  Proof.
    cbv [clobbers PropSet.of_list]; intros.
    intro k'; cbv [map.only_differ PropSet.elem_of] in *. cbn [In].
    lazymatch goal with H : forall k : K, _ |- _ => specialize (H k') end.
    destr (key_eqb k k'); rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
    all:tauto.
  Qed.

  Lemma clobbers_step_if l k v r1 r2 :
    clobbers l r1 r2 ->
    clobbers (if existsb (key_eqb k) l then l else k :: l) r1 (map.put r2 k v).
  Proof.
    intros.
    pose proof List.existsb_eqb_in k l.
    destr (existsb (key_eqb k) l).
    { apply clobbers_step_in; tauto. }
    { apply clobbers_step. auto. }
  Qed.

  Lemma clobbers_not_in l r1 r2 x v :
    clobbers l r1 r2 ->
    map.get r1 x = Some v ->
    ~ (In x l) ->
    map.get r2 x = Some v.
  Proof.
    cbv [clobbers map.only_differ PropSet.of_list PropSet.elem_of]; intros.
    lazymatch goal with H : forall x : K, _ \/ _ |- _ =>
                          destruct (H ltac:(eassumption)) end.
    all:try tauto; congruence.
  Qed.

  Lemma clobbers_trans :
    forall l1 l2 r1 r2 r3,
      clobbers l1 r1 r2 ->
      clobbers l2 r2 r3 ->
      clobbers (l1 ++ l2) r1 r3.
  Proof.
    cbv [clobbers]; intros.
    eapply map.only_differ_trans; eauto; [ ].
    rewrite PropSet.of_list_app_eq. reflexivity.
  Qed.

  Lemma clobbers_trans_dedup l1 l2 l3 r1 r2 r3 :
      clobbers l1 r1 r2 ->
      clobbers l2 r2 r3 ->
      l3 = List.dedup key_eqb (l1 ++ l2) ->
      clobbers l3 r1 r3.
  Proof.
    intros; subst.
    eapply map.only_differ_subset;
      [ | eapply map.only_differ_trans; eauto; reflexivity ].
    cbv [PropSet.of_list PropSet.subset PropSet.union PropSet.elem_of].
    intros. rewrite <-List.dedup_preserves_In.
    auto using in_or_app.
  Qed.

  Lemma clobbers_incl l1 l2 r1 r2 :
    clobbers l1 r1 r2 ->
    incl l1 l2 ->
    clobbers l2 r1 r2.
  Proof.
    cbv [incl clobbers map.only_differ PropSet.elem_of PropSet.of_list].
    intros; subst. repeat lazymatch goal with H : forall x : K, _ |- _ =>
                                                specialize (H ltac:(eassumption)) end.
    intuition idtac.
  Qed.
End __.

(* initialize register tracking at the start of the proof *)
Ltac track_registers_init :=
  let regs := lazymatch goal with
              | |- context [otbn_busy _ ?regs] => regs end in
  let wregs := lazymatch goal with
              | |- context [otbn_busy _ _ ?wregs] => wregs end in
  let flags := lazymatch goal with
              | |- context [otbn_busy _ _ _ ?flags] => flags end in
  let regs' := fresh "regs" in
  let wregs' := fresh "wregs" in
  let flags' := fresh "flags" in
  let Hr := fresh in
  remember regs as regs' eqn:Hr;
  assert (clobbers [] regs regs')
    by (cbv [clobbers]; subst regs'; right; reflexivity);
  let Hw := fresh in
  remember wregs as wregs' eqn:Hw;
  assert (clobbers [] wregs wregs')
    by (cbv [clobbers]; subst wregs'; right; reflexivity);
  let Hf := fresh in
  remember flags as flags' eqn:Hf;
  assert (clobbers [] flags flags')
    by (cbv [clobbers]; subst flags'; right; reflexivity);
  rewrite Hr, Hw, Hf;
  (* rewrite back in postcondition but not state *)
  lazymatch goal with
  | |- context [otbn_busy ?pc regs wregs flags] =>
      replace (otbn_busy pc regs wregs flags) with (otbn_busy pc regs' wregs' flags')
      by (rewrite Hr, Hw, Hf; reflexivity)
  end;
  clear Hr Hw Hf.

Ltac update_clobbers k l v H :=  
  let H' := fresh in
  pose proof (clobbers_step_if l k v _ _ H) as H';
  cbn [existsb orb gpr_eqb csr_eqb reg_eqb wdr_eqb wsr_eqb wreg_eqb flag_group_eqb FG0 FG1 flag_eqb] in H'.
Ltac update_live_registers r k v r' :=
  let Heq := fresh in
  remember (map.put r k v) as r' eqn:Heq;
  assert (map.get r' k = Some v) by (subst r'; apply map.get_put_same);
  repeat lazymatch goal with
    | H : map.get r k = Some _ |- _ => clear H
    | H : map.get r ?k = Some ?v |- _ =>
        assert (map.get r' k = Some v)
        by (subst r'; rewrite map.get_put_diff by congruence; eauto);
        clear H
    end;
  clear Heq.

Local Ltac find_innermost_put e :=
  lazymatch e with
  | map.put (map.put ?m ?k1 ?v1) ?k2 ?v2 =>
      find_innermost_put (map.put m k1 v1)
  | map.put ?m ?k ?v => e
  end.

Local Ltac update_tracking m1 m0 k v :=
  let T := lazymatch type of m0 with @map.rep ?T _ _ => T end in
  lazymatch find_innermost_put (map.put m0 k v) with
  | map.put ?m0 ?k ?v =>
      lazymatch goal with
      | H : @clobbers T _ _ ?l ?m ?m0 |- _ =>
          let v' := fresh "v" in
          set (v':= v);
          update_clobbers k l v' H;
          update_live_registers m0 k v' m1;
          clear H m0
      | _ => fail "Could not find hypothesis for clobbered values of type" T
      end
  end.
           
Local Ltac track_registers_update_step :=
  lazymatch goal with
  | |- context [otbn_busy _ (map.put ?regs0 ?k ?v)] =>
      let regs1 := fresh "regs" in
      update_tracking regs1 regs0 k v
  | |- context [otbn_busy _ _ (map.put ?wregs0 ?k ?v)] =>
      let wregs1 := fresh "wregs" in
      update_tracking wregs1 wregs0 k v
  | |- context [otbn_busy _ _ _ (map.put ?flags0 ?k ?v)] =>
      let flags1 := fresh "flags" in
      update_tracking flags1 flags0 k v
  | _ => idtac (* nothing was updated *)
  end.

(* Run after processing an instruction to update register tracking *)
Ltac track_registers_update :=
  track_registers_update_step; repeat progress track_registers_update_step.

Local Ltac infer_eqb_for_type T :=
  let eqb_spec := constr:(_:forall x y : T, BoolSpec (x = y) (x <> y) (_ x y)) in
  let eqb := lazymatch type of eqb_spec with Decidable.EqDecider ?f => f end in
  eqb.
Local Ltac combine_clobbers m2 :=
  lazymatch goal with
  | H0 : clobbers ?l0 ?m0 ?m1, H1 : clobbers ?l1 ?m1 m2 |- _ =>
      repeat lazymatch goal with
        | H : map.get m1 ?r = _ |- _ =>
            try (let Hnin := fresh in
                 assert (~ In r l1) as Hnin by (cbv [In]; intuition congruence);
                 pose proof (clobbers_not_in l1 _ _ _ _ H1 H Hnin);
                 clear Hnin);
            clear H
        end;
      let T := lazymatch type of l0 with list ?T => T end in
      let eqb := infer_eqb_for_type T in
      let l2 := (eval vm_compute in (List.dedup eqb (l0 ++ l1))) in
      pose proof (clobbers_trans_dedup (key_eqb:=eqb)
                    _ _ l2 _ _ _ H0 H1 ltac:(reflexivity));
      clear H0 H1; try clear m1
  | _ => idtac
  end.

(* use after a jump to combine the postconditions *)
Ltac track_registers_combine :=
  lazymatch goal with
  | |- context [otbn_busy _ ?regs ?wregs ?flags] =>
      combine_clobbers regs;
      combine_clobbers wregs;
      combine_clobbers flags
  end.

Ltac check_register_tracking :=
  lazymatch goal with
  | H : clobbers _ _ ?regs0 |- context [?regs0] => idtac
  | _ => fail "cannot find register tracking; did you run track_registers_init?"
  end.

Ltac init_register_tracking_if_missing :=
  first [ check_register_tracking
        | track_registers_init ].

Ltac solve_clobbers :=
  lazymatch goal with
  | |- clobbers _ ?x ?x => solve [eapply map.only_differ_same]
  | H : clobbers ?l ?x ?y |- clobbers ?l ?x ?y => exact H
  | H : clobbers ?l1 ?x ?y |- clobbers ?l2 ?x ?y =>
      apply (clobbers_incl l1 l2); cbv [incl In]; tauto
  | |- clobbers ?l ?x ?y =>
      fail "solve_clobbers: no matching clobbers clause found for goal: clobbers" l x y
  | _ => fail "solve_clobbers: expected a goal of the form: clobbers _ _ _"
  end.
