Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

(*** Tactic that attempts to simplify, maybe solve goals with `map.get` and `map.put`. ***)

(* Just helpful for debugging, it's annoying when mapsimpl fails
   because I forgot a context variable *)
Local Ltac print_warning_if_no_mapok :=
  (* somewhat counterintuitively, the multimatch fails if all map
     instances have map.ok instances; this is to force the multimatch
     to keep looking for *missing* map.oks instead of stopping at the
     first map instance that has one. `try` prevents the whole tactic
     from failing. *)
  try multimatch goal with
    | map : map.map ?K ?V |- _ =>
        lazymatch goal with
        | map_ok : map.ok map |- _ => fail (* make the multimatch look again *)
        | _ => idtac "Warning: no map.ok instance found for" map ": map.map" K V
        end
    end.

Ltac mapsimpl_step t :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | H : ?P |- ?P => exact H
  | |- context [ map.get map.empty _ ] =>
      rewrite map.get_empty
  | |- context [ map.get (map.put _ ?k _) ?k ] =>
      rewrite map.get_put_same
  | |- context [ map.put (map.put _ ?k _) ?k ] =>
      rewrite map.put_put_same
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
Ltac mapsimpl :=
  print_warning_if_no_mapok;
  repeat (mapsimpl_step ltac:(congruence)).
