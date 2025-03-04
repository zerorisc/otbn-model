Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedListWord.
Require Import Otbn.Model.
Import ListNotations.
Import Otbn.Model.Coercions.
Local Open Scope Z_scope.

Module SortedListRegs.
  Definition ltb (r1 r2 : reg) := String.ltb (reg_to_string r1) (reg_to_string r2).
  Definition Build_parameters (T : Type) : SortedList.parameters.parameters :=
    {|
      SortedList.parameters.key := reg;
      SortedList.parameters.value := T;
      SortedList.parameters.ltb := ltb;
    |}.
  Definition strict_order : SortedList.parameters.strict_order ltb.
  Proof.
    cbv [ltb]; constructor; intros.
    { abstract (cbv [reg_to_string gpr_to_string csr_to_string];
                repeat destruct_one_match; apply eq_refl). }
    { abstract (eauto using String.ltb_trans). }
    { abstract (cbv [reg_to_string gpr_to_string csr_to_string] in *;
                repeat destruct_one_match_hyp; try reflexivity;
                exfalso; cbv in *; try congruence). }
  Defined.

  Global Instance map : map.map reg Naive.word32 :=
    SortedList.map (Build_parameters _) strict_order.
End SortedListRegs.

Module SortedListWregs.
  Definition ltb (r1 r2 : wreg) := String.ltb (wreg_to_string r1) (wreg_to_string r2).
  Definition Build_parameters (T : Type) : SortedList.parameters.parameters :=
    {|
      SortedList.parameters.key := wreg;
      SortedList.parameters.value := T;
      SortedList.parameters.ltb := ltb;
    |}.
  Definition strict_order : SortedList.parameters.strict_order ltb.
  Proof.
    cbv [ltb]; constructor; intros.
    { abstract (cbv [wreg_to_string wdr_to_string wsr_to_string];
                repeat destruct_one_match; apply eq_refl). }
    { abstract (eauto using String.ltb_trans). }
    { abstract (cbv [wreg_to_string wdr_to_string wsr_to_string] in *;
                repeat destruct_one_match_hyp; try reflexivity;
                exfalso; cbv in *; try congruence). }
  Defined.

  Global Instance map : map.map wreg Naive.word256 :=
    SortedList.map (Build_parameters _) strict_order.
End SortedListWregs.

Module SortedListFlags.
  Definition ltb (f1 f2 : flag) := String.ltb (flag_to_string f1) (flag_to_string f2).
  Definition Build_parameters (T : Type) : SortedList.parameters.parameters :=
    {|
      SortedList.parameters.key := flag;
      SortedList.parameters.value := T;
      SortedList.parameters.ltb := ltb;
    |}.
  Definition strict_order : SortedList.parameters.strict_order ltb.
  Proof.
    cbv [ltb]; constructor; intros.
    { abstract (cbv [flag_to_string flag_group_to_string];
                repeat destruct_one_match; apply eq_refl). }
    { abstract (eauto using String.ltb_trans). }
    { abstract (cbv [flag_to_string flag_group_to_string] in *;
                repeat destruct_one_match_hyp; try reflexivity;
                exfalso; cbv in *; try congruence). }
  Defined.

  Global Instance map : map.map flag bool :=
    SortedList.map (Build_parameters _) strict_order.
End SortedListFlags.

Global Instance mem : map.map Naive.word32 Byte.byte := SortedListWord.map _ _.

Module ExecTest.
  Local Instance word32 : word.word 32 := Naive.word 32.
  Local Instance word256 : word.word 256 := Naive.word 256.
  (* Check that exec works *)
  Eval vm_compute in
    (exec1 (fetch:=fetch Test.prog0) (start_state map.empty)).
  Eval vm_compute in
    (exec (fetch:=fetch Test.prog0) (start_state map.empty) 100).

  (* scaling factor; create a program with ~n instructions *)
  Definition n := 10000.
  Definition add_fn : otbn_function := Eval vm_compute in (Test.repeat_add 10000).
  Definition start_fn : otbn_function :=
    ("start",
      map.empty,
      [ (Addi x3 x0 23 : insn);
        (Jal x1 (fst (fst add_fn)) : insn);
        (Sw x0 x2 0 : insn);
        (* Uncomment this line to see an error
        (Addi x2 x5 0 : insn);
        *)
        (Ecall : insn)])%string.

  (* Check that exec completes in a reasonable amount of time *)
  Definition prog : program := ltac:(link_program [start_fn; add_fn]).
  Time
    Eval vm_compute in
    (exec (fetch:=fetch prog) (start_state map.empty) (length prog)).
  (* 5s *)

End ExecTest.
