Require Import coqutil.Tactics.Tactics.
Require Import Otbn.ISA.

(* Boilerplate definitions for comparing registers. *)

Local Ltac derive_eqb r1 r2 :=
  pose r1 as x1;
  pose r2 as x2;
  destruct r1, r2;
  lazymatch goal with
  | x1 := ?x, x2 := ?x |- _ => clear; exact true
  | _ => clear; exact false
  end.
Local Ltac prove_eqb_spec r1 r2 :=
  destruct r1, r2; constructor; congruence.
  
Definition gpr_eqb (r1 r2 : gpr) : bool.
Proof. derive_eqb r1 r2. Defined.
Definition csr_eqb (r1 r2 : csr) : bool.
Proof. derive_eqb r1 r2. Defined.
Definition reg_eqb (r1 r2 : reg) : bool :=
  match r1, r2 with
  | gpreg r1, gpreg r2 => gpr_eqb r1 r2
  | csreg r1, csreg r2 => csr_eqb r1 r2
  | _, _ => false
  end.

Global Instance gpr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (gpr_eqb r1 r2).
Proof. prove_eqb_spec r1 r2. Qed.
Global Instance csr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (csr_eqb r1 r2).
Proof. prove_eqb_spec r1 r2. Qed.
Global Instance reg_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (reg_eqb r1 r2).
Proof.
  destruct r1, r2; cbn [reg_eqb];
    repeat lazymatch goal with
      | |- BoolSpec _ _ (?eqb ?x ?y) => destr (eqb x y)
      | _ => constructor; congruence
      end.
Qed.

Definition wdr_eqb (r1 r2 : wdr) : bool.
Proof. derive_eqb r1 r2. Defined.
Definition wsr_eqb (r1 r2 : wsr) : bool.
Proof. derive_eqb r1 r2. Defined.
Definition wreg_eqb (r1 r2 : wreg) : bool :=
  match r1, r2 with
  | wdreg r1, wdreg r2 => wdr_eqb r1 r2
  | wsreg r1, wsreg r2 => wsr_eqb r1 r2
  | _, _ => false
  end.

Global Instance wdr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wdr_eqb r1 r2).
Proof. prove_eqb_spec r1 r2. Qed.
Global Instance wsr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wsr_eqb r1 r2).
Proof. prove_eqb_spec r1 r2. Qed.
Global Instance wreg_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wreg_eqb r1 r2).
Proof.
  destruct r1, r2; cbn [wreg_eqb];
    repeat lazymatch goal with
      | |- BoolSpec _ _ (?eqb ?x ?y) => destr (eqb x y)
      | _ => constructor; congruence
      end.
Qed.

Definition flag_group_eqb (fg1 fg2 : flag_group) : bool.
Proof. derive_eqb fg1 fg2. Defined.
Definition flag_eqb (f1 f2 : flag) : bool :=
  match f1, f2 with
  | flagM fg1, flagM fg2 => flag_group_eqb fg1 fg2
  | flagL fg1, flagL fg2 => flag_group_eqb fg1 fg2
  | flagZ fg1, flagZ fg2 => flag_group_eqb fg1 fg2
  | flagC fg1, flagC fg2 => flag_group_eqb fg1 fg2
  | _, _ => false
  end.

Global Instance flag_group_eqb_spec :
  forall fg1 fg2, BoolSpec (fg1 = fg2) (fg1 <> fg2) (flag_group_eqb fg1 fg2).
Proof. prove_eqb_spec fg1 fg2. Qed.
Global Instance flag_eqb_spec : forall f1 f2, BoolSpec (f1 = f2) (f1 <> f2) (flag_eqb f1 f2).
Proof.
  destruct f1, f2; cbn [flag_eqb];
    repeat lazymatch goal with
      | |- BoolSpec _ _ (?eqb ?x ?y) => destr (eqb x y)
      | _ => constructor; congruence
      end.
Qed.
