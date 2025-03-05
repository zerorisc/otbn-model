(* Simple utility tactic that substitutes terms into the goal. *)
Ltac subst_lets_step :=
  multimatch goal with
  | x := _ |- _ => lazymatch goal with |- context [x] => subst x end
  end.
Ltac subst_lets := repeat subst_lets_step.
