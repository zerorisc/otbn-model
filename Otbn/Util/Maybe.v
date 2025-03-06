Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* Everyone has their own error monad and this one is mine *)
(* returns either a value or an error message, helpful for debugging *)

Definition maybe (A : Type) : Type := A + string.
Definition bind {A B} (x : maybe A) (f : A -> maybe B) : maybe B :=
  match x with
  | inl a => f a
  | inr err => inr err
  end.
Definition map_err {A} (x : option A) (err : string) : maybe A :=
  match x with
  | Some v => inl v
  | None => inr err
  end.
Definition prefix_err {A} (x : maybe A) (prefix : string) : maybe A :=
  match x with
  | inl v => inl v
  | inr err => inr (prefix ++ err)%string
  end.
Definition maybe_map {A B} (f : A -> B) (x : maybe A) : maybe B :=
  match x with
  | inl v => inl (f v)
  | inr err => inr err
  end.
Fixpoint maybe_fold_left {A B} (f : A -> B -> maybe A) (l : list B) (x : A) : maybe A :=
  match l with
  | [] => inl x
  | b :: l =>
      bind (f x b) (maybe_fold_left f l)
  end.
Fixpoint maybe_flat_map {A B} (f : A -> maybe (list B)) (l : list A) : maybe (list B) :=
  match l with
  | [] => inl []
  | a :: l =>
      bind (f a) (fun l1 => bind (maybe_flat_map f l) (fun l2 => inl (l1 ++ l2)))
  end.
Definition assertion (cond : bool) (msg : string) : maybe unit :=
  if cond then inl tt else inr msg.

Module MaybeNotations.
  Declare Scope maybe_scope.
  Delimit Scope maybe_scope with maybe.
  Notation "a <- b ; c" := (bind b (fun a => c)) (at level 100, right associativity) : maybe_scope.
  Notation Ok := inl (only parsing).
  Notation "'Err' x" := (inr x%string) (at level 20, only parsing) : maybe_scope.
End MaybeNotations.

Require Import coqutil.Tactics.Tactics.

Ltac maybe_simpl_step :=
  lazymatch goal with
  | H : inl ?a = inl ?b |- _ => assert (a = b) by congruence; clear H; subst
  | H : inl _ = inr _ |- _ => congruence
  | H : inr _ = inl _ |- _ => congruence
  | H : (?a, ?b) = (?c, ?d) |- _ =>
      assert (a = c) by congruence;
      assert (b = d) by congruence;
      clear H; subst
  | H : context [bind ?x] |- _ => destr x; cbn [bind] in H
  | |- context [bind ?x] => destr x; cbn [bind]
  | _ => progress cbn [bind] in *
  end.
Ltac maybe_simpl := repeat maybe_simpl_step.
