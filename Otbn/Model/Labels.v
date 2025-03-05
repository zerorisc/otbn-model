Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Coq.Strings.HexString.

(* Representation of jump locations (e.g. string, numerical offset). *)

Class label_parameters {label : Type} :=
  {
    label_eqb : label -> label -> bool;
    label_to_string : label -> string;
    pc_to_string : label * nat -> string;
  }.
Global Arguments label_parameters : clear implicits.

Class label_parameters_ok {label} (params: label_parameters label) :=
  {
    label_eqb_spec : forall d1 d2, BoolSpec (d1 = d2) (d1 <> d2) (label_eqb d1 d2)
  }.

Instance string_label_parameters : label_parameters string :=
  {|
    label_eqb := String.eqb;
    label_to_string := id;
    pc_to_string := fun pc => (fst pc ++ "+" ++ HexString.of_Z (4 * Z.of_nat (snd pc)))%string;
  |}.

Instance nat_label_parameters : label_parameters nat :=
  {|
    label_eqb := Nat.eqb;
    label_to_string := HexString.of_nat;
    pc_to_string := fun pc => HexString.of_Z (4 * Z.of_nat (fst pc + snd pc));
  |}.
