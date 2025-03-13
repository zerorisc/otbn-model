
(*** Simple utility tactic that substitutes terms into the goal. ***)

Ltac change_in_goal x y :=
  lazymatch goal with | |- ?G =>
                          let P := (eval pattern x in G) in
                          lazymatch P with | ?P _ => change (P y); cbv beta end end.
Ltac subst_lets_step :=
  multimatch goal with
  | x := ?y |- _ =>
           lazymatch goal with |- context [x] => idtac end;
           (* `subst` would inline the let in all the other lets and hypotheses *)
           change_in_goal x y
  end.
Ltac subst_lets := repeat subst_lets_step.
