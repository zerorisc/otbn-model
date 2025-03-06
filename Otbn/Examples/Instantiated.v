Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedListWord.
Require Import Otbn.Examples.Add32.
Require Import Otbn.Examples.RepeatAdd.
Require Import Otbn.ISA.ISA.
Require Import Otbn.ISA.Labels.
Require Import Otbn.Linker.Linker.
Require Import Otbn.ISA.ToString.
Require Import Otbn.Semantics.Semantics.
Require Coq.Strings.HexString.
Import ListNotations.
Import Semantics.Coercions.
Local Open Scope Z_scope.

(*** Fully instantiate an executable, extractable OTBN model. ***)

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

Local Instance word32 : word.word 32 := Naive.word 32.
Local Instance word256 : word.word 256 := Naive.word 256.

(* Pretty-printing (only works on fully computed states! *)
Definition pretty_print_list {A} (A_to_string : A -> string) (l : list A) : string :=
  "[" ++ String.concat ", " (List.map A_to_string l) ++ "]".
Definition pretty_print_map
  {K V} {map : map.map K V} (K_to_string : K -> string) (V_to_string : V -> string) (m : map)
  : string :=
  ("{" ++ (pretty_print_list (fun '(k,v) => K_to_string k ++ ": " ++ V_to_string v)
             (map.tuples m)) ++ "}")%string.
Definition word_to_hex {width} {word : word.word width} w : string :=
  HexString.of_Z (word.unsigned (word:=word) w).
Definition byte_to_hex b : string := HexString.of_N (Byte.to_N b).
Definition bool_to_string (b : bool) : string := if b then "1" else "0".
Definition pretty_print_regs : SortedListRegs.map -> string :=
  pretty_print_map reg_to_string word_to_hex.
Definition pretty_print_wregs : SortedListWregs.map -> string :=
  pretty_print_map wreg_to_string word_to_hex.
Definition pretty_print_flags : SortedListFlags.map -> string :=
  pretty_print_map flag_to_string bool_to_string.
Definition pretty_print_dmem : mem -> string :=
  pretty_print_map word_to_hex byte_to_hex.
Definition pretty_print_cstack {label} {label_params : label_parameters label}
  : list (label * nat) -> string :=
  pretty_print_list label_params.(pc_to_string).
Definition pretty_print_lstack {label} {label_params : label_parameters label}
  : list (label * nat * nat) -> string :=
  pretty_print_list (fun '(pc,iters) =>
                       label_params.(pc_to_string) pc ++ ", " ++ String.of_nat iters)%string.
Definition newline : string := String (Ascii.Ascii false true false true false false false false) "".
Definition pretty_print_otbn_state {label} {label_params : label_parameters label}
  (st : otbn_state) : string :=
  match st with
  | otbn_busy pc regs wregs flags dmem cstack lstack =>
      "BUSY < pc := " ++ label_params.(pc_to_string) pc ++ newline
        ++ "regs := " ++ pretty_print_regs regs ++ ";" ++ newline
        ++ "wregs :=" ++ pretty_print_wregs wregs ++ ";" ++ newline
        ++ "flags :=" ++ pretty_print_flags flags ++ ";" ++ newline
        ++ "mem :=  " ++ pretty_print_dmem dmem ++ ";" ++ newline
        ++ "call stack :=" ++ pretty_print_cstack cstack ++ ";" ++ newline
        ++ "loop stack :=" ++ pretty_print_lstack lstack ++ ">"
  | otbn_done pc dmem =>
      "DONE < pc := " ++ label_params.(pc_to_string) pc ++ newline
        ++ "mem :=  " ++ pretty_print_dmem dmem ++ ">"
  | otbn_error pc errs =>
      "ERROR < pc := " ++ label_params.(pc_to_string) pc ++ newline
        ++ "errs :=  " ++ String.concat "; " errs ++ ">"
  end.
Definition pretty_print {label} {label_params : label_parameters label}
  (st : Maybe.maybe otbn_state) : string :=
  match st with
  | inl st => pretty_print_otbn_state st
  | inr err => ("Error! " ++ err)%string
  end.

(* Check that executing the instantiated model works *)
Eval vm_compute in
    (pretty_print (exec1 (fetch:=fetch add_prog) (start_state map.empty))).
Eval vm_compute in
  (pretty_print (exec (fetch:=fetch add_prog) (start_state map.empty) 100)).

(* Test scaling: create a program with ~n instructions *)
Definition n := 10000.
Definition add_fn : otbn_function := Eval vm_compute in (repeat_add 10000).
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
Timeout 10
  Time
  Eval vm_compute in
  (pretty_print (exec (fetch:=fetch prog) (start_state map.empty) (length prog))).
(* ~5s *)
