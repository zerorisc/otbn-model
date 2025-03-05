Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.PushPullMod.
Local Open Scope Z_scope.

(*** Generic utility lemmas about `map`s. ***)

Module map.
  Section Generic.
    Context {K V : Type} {map : map.map K V} {map_ok : map.ok map}.
    Context {key_eqb : K -> K -> bool}
      {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

    Lemma only_differ_trans (m1 m2 m3 : map.rep (map:=map)) (s1 s2 s3 : PropSet.set K) :
      map.only_differ m1 s1 m2 ->
      map.only_differ m2 s2 m3 ->
      PropSet.subset (PropSet.union s1 s2) s3 ->
      map.only_differ m1 s3 m3.
    Proof using Type.
      intros. intro k.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : map.only_differ _ _ _ |- _ => specialize (H k)
             | H : PropSet.elem_of _ ?s,
                 H' : PropSet.subset (PropSet.union _ ?s) ?s'
               |- PropSet.elem_of _ ?s' \/ _ =>
                 left; apply H'; apply PropSet.in_union_r; assumption
             | H : PropSet.elem_of _ ?s,
                 H' : PropSet.subset (PropSet.union ?s _) ?s'
               |- PropSet.elem_of _ ?s' \/ _ =>
                 left; apply H'; apply PropSet.in_union_l; assumption
             | H : ?a = ?b, H' : ?b = ?c |- _ \/ ?a = ?c => right; congruence
             end.
    Qed.

    Lemma only_differ_put (m : map.rep (map:=map)) k v s :
      PropSet.subset (PropSet.singleton_set k) s ->
      map.only_differ m s (map.put m k v).
    Proof using map_ok key_eqb_spec.
      intros. cbv [map.only_differ PropSet.elem_of PropSet.subset PropSet.singleton_set] in *.
      intro k'. destr (key_eqb k k'); [ left; solve [auto] | right ].
      rewrite map.get_put_diff; congruence.
    Qed.

    Lemma only_differ_subset (m1 m2 : map.rep (map:=map)) s1 s2 :
      PropSet.subset s1 s2 ->
      map.only_differ m1 s1 m2 ->
      map.only_differ m1 s2 m2.
    Proof using Type.
      clear key_eqb key_eqb_spec.
      intros. cbv [map.only_differ PropSet.elem_of PropSet.subset] in *.
      intro k.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : forall x : K, _ |- _ => specialize (H k)
             | _ => tauto
             end.
    Qed.

    Lemma only_differ_same (m : map.rep (map:=map)) s :
      map.only_differ m s m.
    Proof using Type. right; reflexivity. Qed.
  End Generic.

  Section WordMap.
    Context {width} {word : word.word width} {word_ok : word.ok word}.
    Context {V : Type} {map : map.map word V} {map_ok : map.ok map}.
    
    Lemma get_of_list_word_at_None (a : word) (xs : list V) (i : word) :
        map.get (map.of_list_word_at a xs) i = None <->
          (word.unsigned (word.sub i a) < 0
           \/ Z.of_nat (length xs) <= word.unsigned (word.sub i a)).
    Proof.
      intros. pose proof word.unsigned_range (word.sub i a).
      rewrite map.get_of_list_word_at, nth_error_None.
      rewrite Nat2Z.inj_le, ?Znat.Z2Nat.id; intuition.
    Qed.

    Lemma of_list_word_at_get_pred (addr : word) (vs : list V) :
      Z.of_nat (length vs) < 2^width ->
      map.get (map.of_list_word_at (word.add addr (word.of_Z 1)) vs) addr = None.
    Proof.
      intros; pose proof word.width_pos.
      pose proof proj1 (Z.pow_gt_1 2 width ltac:(lia)) ltac:(lia).
      eapply get_of_list_word_at_None. right.
      rewrite word.unsigned_sub, word.unsigned_add, word.unsigned_of_Z_1.
      cbv [word.wrap]. Z.push_pull_mod.
      rewrite Z.sub_add_distr. rewrite Z.sub_diag, Z.sub_0_l.
      rewrite Z.mod_opp_l_nz by (rewrite ?Z.mod_small by lia; lia).
      rewrite Z.mod_small by lia. lia.
    Qed.
  End WordMap.
End map.

Section Separation.
  Context {K V} {map : map.map K V} {map_ok : map.ok map}.
  Context {key_eqb : K -> K -> bool}
    {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

  Lemma sep_put_iff1 (m : map) k v :
    map.get m k = None -> Lift1Prop.iff1 (eq (map.put m k v)) (ptsto k v * eq m)%sep.
  Proof.
    repeat intro. cbv [sep ptsto]. split; intros; subst.
    { do 2 eexists; ssplit; eauto.
      eapply map.split_put_r2l; eauto; [ ].
      eapply map.split_empty_l; reflexivity. }
    { repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : map.split _ (map.put map.empty _ _) _ |- _ =>
                 apply map.split_put_l2r in H; [ | solve [apply map.get_empty ] ];
                 eapply map.split_empty_l in H
             | |- ?x = ?x => reflexivity
             | _ => progress subst
             end. }
  Qed.
End Separation.

(* Tactic that attempts to simplify and solve goals with `map.get` *)
Ltac mapsimpl_step t :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | H : ?P |- ?P => exact H
  | |- context [ map.get (map.put _ ?k _) ?k ] =>
      rewrite map.get_put_same
  | |- context [ map.get (map.put ?m ?k1 ?v) ?k2 ] =>
      first [ rewrite (map.get_put_diff m k2 v k1) by t
            | replace k1 with k2 by t; rewrite map.get_put_same ]
  | H : map.get ?m ?k = _ |- context [map.get ?m ?k] =>
      rewrite H
  | _ => match goal with
         | m := _ : map.rep |- _ =>
                  lazymatch goal with |- context [m] => subst m end
         end
  end.
Ltac mapsimpl := repeat (mapsimpl_step ltac:(congruence)).

