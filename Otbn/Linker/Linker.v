Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedListString.
Require Import Otbn.ISA.ISA.
Require Import Otbn.Util.Maybe.
Require Import Otbn.ISA.Labels.
Require Import Otbn.Semantics.Semantics.
Import ListNotations.
Import MaybeNotations.
Local Open Scope maybe_scope.

(*** Contains a linker for OTBN programs. ***)

Definition add_symbol (syms : symbols) (label : string) (offset : nat)
  : maybe symbols :=
  match map.get syms label with
  | Some _ => Err ("Symbol " ++ label ++ " appears more than once.")
  | None => Ok (map.put syms label offset)
  end.

Definition merge_symbols
  (global_offset : nat) (global_syms fn_syms : symbols) : maybe symbols :=
  map.fold
    (fun global_syms label fn_offset =>
       (global_syms <- global_syms ;
        add_symbol global_syms label (global_offset + fn_offset)))
    (Ok global_syms) fn_syms.

(* Returns the symbols plus the overall size of the program *)
Definition link_symbols_for_function
  (syms_offset : symbols * nat) (fn : otbn_function) : maybe (symbols * nat) :=
  let fn_name := fst (fst fn) in
  let fn_syms := snd (fst fn) in
  let fn_insns := snd fn in
  (syms <- add_symbol (fst syms_offset) fn_name (snd syms_offset) ;
   syms <- merge_symbols (snd syms_offset) syms fn_syms ;
   Ok (syms, (snd syms_offset + length fn_insns)%nat)).
Definition link_symbols'
  (start_syms : symbols)
  (start_offset : nat)
  (fns : list otbn_function)
  : maybe (symbols * nat) :=
  maybe_fold_left link_symbols_for_function fns (start_syms, start_offset).
Definition link_symbols (fns : list otbn_function) : maybe symbols :=
  (syms_offset <- link_symbols' map.empty 0%nat fns ;
   Ok (fst syms_offset)).

Definition link_cinsn
  (syms : map.rep (map:=symbols)) (i : cinsn (label:=string))
  : maybe (cinsn (label:=nat)) :=
  match i with
  | Ret => Ok Ret
  | Ecall => Ok Ecall
  | Unimp => Ok Unimp
  | Jal r dst =>
      (dst <- map_err (map.get syms dst) ("Label " ++ dst ++ " not found (jal)");
       Ok (Jal r dst))
  | Bne r1 r2 dst =>
      (dst <- map_err (map.get syms dst) ("Label " ++ dst ++ " not found (bne)");
       Ok (Bne r1 r2 dst))
  | Beq r1 r2 dst =>
      (dst <- map_err (map.get syms dst) ("Label " ++ dst ++ " not found (beq)");
       Ok (Beq r1 r2 dst))
  | Loop r => Ok (Loop r)
  | Loopi imm => Ok (Loopi imm)
  | LoopEnd i => Ok (LoopEnd i)
  end.

Definition link_insn
  (syms : symbols) (i : insn (label:=string))
  : maybe (insn (label:=nat)) :=
  match i with
  | Straightline i => Ok (Straightline i)
  | Control i =>
      (i <- link_cinsn syms i ;
       Ok (Control i))
  end.

Fixpoint link_insns
  (syms : symbols) (insns : list (insn (label:=string)))
  : maybe (list (insn (label:=nat))) :=
  match insns with
  | [] => Ok []
  | i :: insns =>
      (i <- link_insn syms i ;
       insns <- link_insns syms insns ;
       Ok (i :: insns))
  end.

Definition link'
  (syms : symbols) (prog : program) (fn : otbn_function) : maybe program :=
  (fn_insns <- link_insns syms (snd fn) ;
   Ok (prog ++ fn_insns)).

Definition link (fns : list otbn_function) : maybe program :=
  (syms <- link_symbols fns ;
   maybe_fold_left (link' syms) fns []).

Definition cinsn_equiv (syms : symbols)
  (i1 : cinsn (label:=string))
  (i2 : cinsn (label:=nat)) : Prop :=
  match i1, i2 with
  | Ret, Ret => True
  | Ecall, Ecall => True
  | Unimp, Unimp => True
  | Jal r1 dst1, Jal r2 dst2 =>
      r1 = r2 /\ map.get syms dst1 = Some dst2
  | Bne a1 b1 dst1, Bne a2 b2 dst2 =>
      a1 = a2 /\ b1 = b2 /\ map.get syms dst1 = Some dst2
  | Beq a1 b1 dst1, Beq a2 b2 dst2 =>
      a1 = a2 /\ b1 = b2 /\ map.get syms dst1 = Some dst2
  | Loop r1, Loop r2 => r1 = r2
  | Loopi n1, Loopi n2 => n1 = n2
  | LoopEnd i1, LoopEnd i2 => i1 = i2
  | _, _ => False
  end.
    
(* States that a pre-link instruction and post-link instructions are
   equivalent under a given symbol mapping. *)
Definition insn_equiv (syms : symbols)
  (i1 : insn (label:=string))
  (i2 : insn (label:=nat)) : Prop :=
  match i1, i2 with
  | Straightline i1, Straightline i2 => i1 = i2
  | Control i1, Control i2 => cinsn_equiv syms i1 i2
  | _, _ => False
  end.

(* States that a particular (pre-link) function is linked into a
   particular program at the given global offset. *)
Definition linked_at
  (prog : program) (syms : symbols)
  (fn : otbn_function) (global_offset : nat) : Prop :=
  forall fn_offset : nat,
    (fn_offset < length (snd fn))%nat ->
    exists i1 i2,
      fetch_fn fn (fst (fst fn), fn_offset) = Some i1
      /\ fetch prog (global_offset, fn_offset) = Some i2
      /\ insn_equiv syms i1 i2.

(* Run the linker to compute the fully linked version of a program *)
Ltac link_program fns :=
  let val := eval vm_compute in (link fns) in
    lazymatch val with
    | inl ?x => exact x
    | inr ?e => fail e
    end.
