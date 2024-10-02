Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Coq.Strings.HexString.
Import ListNotations.
Local Open Scope Z_scope.

(*** Simplistic machine. ***)
(* This is intended for quick prototyping. The machine has just a few
   registers and instructions; it has neither memory nor flags. *)

Section Registers.
  (* General data registers, 32 bits each. *)
  (* x0 is always wired to 0, x1 is the call stack. *)
  Inductive gpr : Type :=
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7.

  (* Control and status registers, 32-bits each. *)
  Inductive csr : Type :=
  | CSR_RND
  .

  (* Catchall type indicating any register. *)
  Inductive reg :=
  | gpreg : gpr -> reg
  | csreg : csr -> reg
  .
End Registers.

Section ISA.
  (* Straightline instructions (no control flow) *)
  Inductive sinsn : Type :=
  | Addi : gpr -> gpr -> Z -> sinsn
  | Add : gpr -> gpr -> gpr -> sinsn
  | Csrrs : csr -> gpr -> sinsn
  .

  (* Control-flow instructions *)
  Inductive cinsn {destination : Type} : Type :=
  (* TODO: technically ret is a special case of JALR, but only RET is used in practice *)
  | Ret : cinsn
  | Ecall : cinsn
  | Jal : gpr -> destination -> cinsn
  | Bne : gpr -> gpr -> destination -> cinsn
  | Beq : gpr -> gpr -> destination -> cinsn
  (* Note: loops here use an end instruction instead of an iteration
     count to make codegen and processing easier. *)
  | Loop : gpr -> cinsn
  | Loopi : nat -> cinsn
  | LoopEnd : cinsn
  .

  Inductive insn {destination : Type} : Type :=
  | Straightline : sinsn -> insn
  | Control : cinsn (destination:=destination) -> insn
  .
End ISA.

(* Boilerplate definitions for comparing registers. *)
Section RegisterEquality.
  Local Ltac derive_eqb r1 r2 :=
    pose r1 as x1;
    pose r2 as x2;
    destruct r1, r2;
    lazymatch goal with
    | x1 := ?x, x2 := ?x |- _ => clear; exact true
    | _ => clear; exact false
    end.
  
  Definition gpr_eqb (r1 r2 : gpr) : bool.
  Proof. derive_eqb r1 r2. Defined.
  Definition csr_eqb (r1 r2 : csr) : bool.
  Proof. derive_eqb r1 r2. Defined.

  Local Ltac prove_eqb_spec r1 r2 :=
    destruct r1, r2; cbv [gpr_eqb]; constructor; congruence.
  Lemma gpr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (gpr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Lemma csr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (csr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
End RegisterEquality.

Section Stringify.
  Context {destination : Type} {destination_to_string : destination -> string}.
  Local Coercion destination_to_string : destination >-> string.

  Definition gpr_to_string (r : gpr) : string :=
    match r with
    | x0 => "x0"
    | x1 => "x1"
    | x2 => "x2"
    | x3 => "x3"
    | x4 => "x4"
    | x5 => "x5"
    | x6 => "x6"
    | x7 => "x7"
    end.
  Local Coercion gpr_to_string : gpr >-> string.

  Definition csr_to_string (r : csr) : string :=
    match r with
    | CSR_RND => "CSR_RND"
    end.
  Local Coercion csr_to_string : csr >-> string.

  Definition sinsn_to_string (i : sinsn) : string :=
    match i with
    | Addi rd rs imm =>
        "addi " ++ rd ++ ", " ++ rs ++ ", " ++ HexString.of_Z imm
    | Add rd rs1 rs2 =>
        "add " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Csrrs rd rs =>
        "csrrs " ++ rd ++ ", " ++ rs ++ ", "
    end.

  Definition cinsn_to_string (i : cinsn (destination:=destination)) : string :=
    match i with
    | Ret => "ret"
    | Ecall => "ecall"
    | Jal r dst => "jal " ++ r ++ ", " ++ dst
    | Bne r1 r2 dst => "bne " ++ r1 ++ ", " ++ r2 ++ ", " ++ dst
    | Beq r1 r2 dst => "beq " ++ r1 ++ ", " ++ r2 ++ ", " ++ dst
    | Loop r => "loop " ++ r
    | Loopi n => "loop " ++ HexString.of_nat n
    | LoopEnd => "loopend"
    end.

  Definition insn_to_string (i : insn) : string :=
    match i with
    | Straightline i => sinsn_to_string i
    | Control i => cinsn_to_string i
    end.

End Stringify.

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

(* Executable model of OTBN. *)
Section Exec.
  (* Parameterize over the representation of jump locations. *)
  Context {destination : Type}
    {destination_eqb : destination -> destination -> bool}
    {destination_eqb_spec :
      forall d1 d2, BoolSpec (d1 = d2) (d1 <> d2) (destination_eqb d1 d2)}.
  Definition advance_pc (pc : destination * nat) := (fst pc, S (snd pc)).

  (* error values for cases that should be unreachable (these can be
     any value and exist mostly to help debugging -- it's easier to
     understand that something went wrong when you see "error_Z" than
     an unexpected 0). *)
  Context {error_Z : Z}.

  (* Parameterize over the map implementation. *)
  Context {regfile : map.map reg Z}
    {fetch : destination * nat -> option (insn (destination:=destination))}.

  (* Really, I want to talk about terminal states -- either a return
     from the subroutine, the end of the program, or an error.

     straightline needs/edits only regs, flags, dmem --> but can error
     control needs/edits callstack, loopstack, pc, needs regs --> can also error 

     need to process through, come out with a Prop in the end via cps style passing
     the prop gives you rnd reasoning much easier
   *)
  Definition is_valid_addi_imm (imm : Z) : Prop :=
    -2048 <= imm <= 2047.

  Definition read_gpr (regs : regfile) (r : gpr) (P : Z -> Prop) : Prop :=
    match r with
    | x0 => P 0 (* x0 always reads as 0 *)
    | x1 =>
        (* TODO: call stack reads are rare in practice; for now, don't model *)
        False
    | _ => exists v, map.get regs (gpreg r) = Some v /\ P v
    end.

  Definition read_csr (regs : regfile) (r : csr) (P : Z -> Prop) : Prop :=
    match r with
    | CSR_RND => forall v, P v
    end.

  Definition cast32 (v : Z) : Z := v &' Z.ones 32.

  Definition write_gpr (regs : regfile) (r : gpr) (v : Z) (P : regfile -> Prop) : Prop :=
    match r with
    | x0 => P regs
    | x1 =>
        (* TODO: this should push to the call stack, but is
           practically never used. For now, don't model this behavior
           and treat it as an error. *)
        False
    | _ => P (map.put regs (gpreg r) (cast32 v))
    end.

  Definition write_csr (regs : regfile) (r : csr) (v : Z) (P : regfile -> Prop) : Prop :=
    match r with
    | CSR_RND => P regs (* writes ignored *)
    end.

  Fixpoint repeat_advance_pc (pc : destination * nat) (n : nat) : destination * nat :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.

  Local Notation call_stack := (list (destination * nat)) (only parsing).
  Local Notation loop_stack := (list (destination * nat * nat)) (only parsing).
  Inductive otbn_state : Type :=
  | otbn_busy (pc : destination * nat) (regs : regfile) (cstack : call_stack) (lstack : loop_stack)
  | otbn_error (pc : destination * nat) (errs : list string)
  | otbn_done (pc : destination * nat) (regs : regfile)
  .  
  Definition start_state (start_pc : destination * nat) : otbn_state :=
    otbn_busy start_pc map.empty [] [].
  Definition get_pc (st : otbn_state) : destination * nat :=
    match st with
    | otbn_busy pc _ _ _ => pc
    | otbn_error pc _ => pc
    | otbn_done pc _ => pc
    end.
  (* Pop an address off the call stack and jump to that location. *)
  Definition call_stack_pop (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists dst,
        hd_error cstack = Some dst
        /\ post (otbn_busy dst regs cstack lstack)
    | _ => post st
    end.
  (* Push the next (one-advanced) PC onto the call stack. *)
  Definition call_stack_push (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        (length cstack < 8)%nat
        /\ post (otbn_busy pc regs ((advance_pc pc) :: cstack) lstack)
    | _ => post st
    end.
  Definition program_exit (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack => post (otbn_done pc regs)
    | _ => post st
    end.
  Definition set_pc
    (st : otbn_state) (pc : destination * nat) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy _ regs cstack lstack => post (otbn_busy pc regs cstack lstack)
    | _ => post st
    end.
  Definition set_regs (st : otbn_state) (regs : regfile) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc _ cstack lstack => post (otbn_busy pc regs cstack lstack)
    | _ => post st
    end.
  Definition next_pc (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack => post (otbn_busy (advance_pc pc) regs cstack lstack)
    | _ => post st
    end.
  Definition read_gpr_from_state (st : otbn_state) (r : gpr) (post : Z -> Prop) : Prop :=
    match st with
    | otbn_busy _ regs _ _ => read_gpr regs r post
    | _ => False
    end.

  (* Begin a new loop. *)
  Definition loop_start
    (st : otbn_state) (iters : nat) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        let start_pc := advance_pc pc in
        (length lstack < 8)%nat
        /\ iters <> 0%nat
        /\ post (otbn_busy start_pc regs cstack ((start_pc, iters) :: lstack))
    | _ => False
    end.

  (* Finish a loop iteration (and potentially the entire loop).
    Expects that the current PC matches the loop-body end PC of the
    first loop stack entry. *)
  Definition loop_end (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists start_addr iters,
        hd_error lstack = Some (start_addr, iters)
        /\ match iters with
           | O => post (otbn_busy (advance_pc pc) regs cstack (tl lstack))
           | S iters =>
               post (otbn_busy start_addr regs cstack
                       ((start_addr, iters) :: tl lstack))
           end
    | _ => False
    end.

  Definition strt1
    (regs : regfile) (i : sinsn) (post : regfile -> Prop) : Prop :=
    match i with
    | Addi d x imm =>
        is_valid_addi_imm imm /\
          read_gpr regs x
            (fun vx =>
               write_gpr regs d (vx + imm) post)
    | Add d x y =>
        read_gpr regs x
          (fun vx =>
             read_gpr regs y
               (fun vy =>
                  write_gpr regs d (vx + vy) post))
    | Csrrs d x =>
        read_gpr regs x
          (fun vx =>
             read_csr regs d
               (fun vd =>
                  write_csr regs d (Z.lxor vd vx) post))
    end.

  (* TODO: is it possible to simplify the address logic here so we can
    directly link "dst" as a block, even if it means repeated terms? *)
  (* TODO: is it necessary to simulate some error conditions? There
     should be a difference between "OTBN had an error", which
     sometimes should in fact happen on some inputs, and "this program
     is not valid" (e.g. out-of-bounds immediate value that cannot be
     encoded). *)
  Definition ctrl1
    (st : otbn_state) (i : cinsn (destination:=destination))
    (post : otbn_state -> Prop) : Prop :=
    match i with
    | Ret =>  call_stack_pop st post
    | Ecall => program_exit st post
    | Jal r dst =>
        match r with
        | x0 => set_pc st (dst, 0%nat) post
        | x1 => call_stack_push st (fun st => set_pc st (dst, 0%nat) post)
        | _ =>
            (* technically it is possible to write the PC to other
               registers but practically this is almost never done, so
               for now we don't model it *)
            False
        end
    | Bne r1 r2 dst =>
        read_gpr_from_state st r1
          (fun v1 =>
             read_gpr_from_state st r2
               (fun v2 =>
                  (v1 = v2 /\ next_pc st post)
                  \/ (v1 <> v2 /\ set_pc st (dst, 0%nat) post)))
    | Beq r1 r2 dst =>
        read_gpr_from_state st r1
          (fun v1 =>
             read_gpr_from_state st r2
               (fun v2 =>
                  (v1 <> v2 /\ next_pc st post)
                  \/ (v1 = v2 /\ set_pc st (dst, 0%nat) post)))
    | Loopi v => loop_start st v post
    | Loop r => read_gpr_from_state st r
                  (fun v => 0 < v /\ loop_start st (Z.to_nat v) post)
    | LoopEnd => loop_end st post
    end.

  Definition run1 (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists i,
        fetch pc = Some i
        /\ match i with
           | Straightline i =>
               strt1 regs i
                 (fun regs =>
                    set_regs st regs
                      (fun st => set_pc st (advance_pc pc) post))
           | Control i => ctrl1 st i post
           end
    | _ => post st
    end.
End Exec.

Section ErrorMonad.
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
End ErrorMonad.
Module ErrorMonadNotations.
  Notation "a <- b ; c" := (bind b (fun a => c)) (at level 100, right associativity).
  Notation Ok := inl (only parsing).
  Notation "'Err' x" := (inr x%string) (at level 20, only parsing).
End ErrorMonadNotations.

Require Import coqutil.Map.SortedListZ.
Require Import coqutil.Map.SortedListString.
Local Coercion Straightline : sinsn >-> insn.
Local Coercion Control : cinsn >-> insn.
 

(* Contains a way to link programs. *)
Section Build.
  (* TODO: how should we now represent programs? All we need is fetch. *)
  (* option: map from string -> list insn, so that all destinations
     that are jumped to need an entry. The list insns can
     overlap. Execution should not pass the end. *)
  (* Can this cause problems with cycles or too much redundancy? *)
  (* option: list insns * map from string -> nat, return tail of list always *)
  (* this is nice from a representation redundancy perspective *)
  (* how about reasoning with objs? *)
  (* different fetch, multiple copies of list insns * map from string -> nat to choose from *)
  (* or maybe each obj needs to be considered separately? *)
  Definition symbols : map.map string nat := SortedListString.map _.
  Import ErrorMonadNotations.

  (* Objects are conceptually just "chunks of instructions that should
     always be linked sequentially." *)
  Definition object : Type := list (insn (destination:=string)).
  (* Functions consist of a name, internal labels (map of string ->
     offset within the function), and a list of instructions. *)
  Definition function : Type := string * symbols * object.
  (* Programs are lists of instructions that link to each other with
     offsets within the global program. This represents code
     post-linking. *)
  Definition program : Type := list (insn (destination:=nat)).

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
    (syms_offset : symbols * nat) (fn : function) : maybe (symbols * nat) :=
    let fn_name := fst (fst fn) in
    let fn_syms := snd (fst fn) in
    let fn_insns := snd fn in
    (syms <- add_symbol (fst syms_offset) fn_name (snd syms_offset) ;
     syms <- merge_symbols (snd syms_offset) syms fn_syms ;
     Ok (syms, (snd syms_offset + length fn_insns)%nat)).
  Definition link_symbols'
    (start_syms : symbols)
    (start_offset : nat)
    (fns : list function)
    : maybe (symbols * nat) :=
    maybe_fold_left link_symbols_for_function fns (start_syms, start_offset).
  Definition link_symbols (fns : list function) : maybe symbols :=
    (syms_offset <- link_symbols' map.empty 0%nat fns ;
     Ok (fst syms_offset)).

  Definition link_cinsn
    (syms : map.rep (map:=symbols)) (i : cinsn (destination:=string))
    : maybe (cinsn (destination:=nat)) :=
    match i with
    | Ret => Ok Ret
    | Ecall => Ok Ecall
    | Jal r dst =>
        (dst <- map_err (map.get syms dst) ("Destination " ++ dst ++ " not found (jal)");
         Ok (Jal r dst))
    | Bne r1 r2 dst =>
        (dst <- map_err (map.get syms dst) ("Destination " ++ dst ++ " not found (bne)");
         Ok (Bne r1 r2 dst))
    | Beq r1 r2 dst =>
        (dst <- map_err (map.get syms dst) ("Destination " ++ dst ++ " not found (beq)");
         Ok (Beq r1 r2 dst))
    | Loop r => Ok (Loop r)
    | Loopi imm => Ok (Loopi imm)
    | LoopEnd => Ok LoopEnd
    end.

  Definition link_insn
    (syms : symbols) (i : insn (destination:=string))
    : maybe (insn (destination:=nat)) :=
    match i with
    | Straightline i => Ok (Straightline i)
    | Control i =>
        (i <- link_cinsn syms i ;
         Ok (Control i))
    end.

  Fixpoint link_insns
    (syms : symbols) (insns : list (insn (destination:=string)))
    : maybe (list (insn (destination:=nat))) :=
    match insns with
    | [] => Ok []
    | i :: insns =>
        (i <- link_insn syms i ;
         insns <- link_insns syms insns ;
         Ok (i :: insns))
    end.

  Definition link'
    (syms : symbols) (prog : program) (fn : function) : maybe program :=
    (fn_insns <- link_insns syms (snd fn) ;
     Ok (prog ++ fn_insns)).

  Definition link (fns : list function) : maybe program :=
    (syms <- link_symbols fns ;
     maybe_fold_left (link' syms) fns []).

  Definition get_label_offset
    (fn : function) (label : string) : option nat :=
    let fn_name := fst (fst fn) in
    let fn_syms := snd (fst fn) in
    if (String.eqb label fn_name)
    then Some 0%nat
    else map.get fn_syms label.

  (* Fetch from a function. *)
  Definition fetch_fn
    (pc : string * nat) (fn : function) : option insn :=
    let label := fst pc in
    let offset := snd pc in
    let fn_insns := snd fn in
    match get_label_offset fn label with
    | None => None
    | Some label_offset => nth_error fn_insns (label_offset + offset)
    end.

  (* TODO: actually need fetch from a whole bunch of functions that
     might link to one another!!!!! maybe need string -> function
     mapping? Or just global symbols? *)
  (* consider options here carefully *)
  (* we want to reason about the program BEFORE LINKING -- should
     still be OK for functions to appear in any order *)
  (* option 1: parameterize over final program, have a "linked @"
     predicate that says for every offset < function length, whole
     program fetch for fn offset + offset is the same insn as fetch
     from function (will also need symbol-table predicate for cinsns
     related) *)
  (* then prove that if fn is in the list and link succeeds, it's
     linked after link at the expected PC *)

  (* Fetch from a whole program. *)
  Definition fetch
    (pc : nat * nat) (prog : program) : option insn :=
    let global_offset := fst pc in
    let fn_offset := snd pc in
    nth_error prog (global_offset + fn_offset).

  Definition cinsn_equiv (syms : symbols)
    (i1 : cinsn (destination:=string))
    (i2 : cinsn (destination:=nat)) : Prop :=
    match i1, i2 with
    | Ret, Ret => True
    | Ecall, Ecall => True
    | Jal r1 dst1, Jal r2 dst2 =>
        r1 = r2 /\ map.get syms dst1 = Some dst2
    | Bne a1 b1 dst1, Bne a2 b2 dst2 =>
        a1 = a2 /\ b1 = b2 /\ map.get syms dst1 = Some dst2
    | Beq a1 b1 dst1, Beq a2 b2 dst2 =>
        a1 = a2 /\ b1 = b2 /\ map.get syms dst1 = Some dst2
    | Loop r1, Loop r2 => r1 = r2
    | Loopi n1, Loopi n2 => n1 = n2
    | LoopEnd, LoopEnd => True
    | _, _ => False
    end.
    
  (* States that a pre-link instruction and post-link instructions are
     equivalent under a given symbol mapping. *)
  Definition insn_equiv (syms : symbols)
    (i1 : insn (destination:=string))
    (i2 : insn (destination:=nat)) : Prop :=
    match i1, i2 with
    | Straightline i1, Straightline i2 => i1 = i2
    | Control i1, Control i2 => cinsn_equiv syms i1 i2
    | _, _ => False
    end.

  (* States that a particular (pre-link) function is linked into a
     particular program at the given global offset. *)
  Definition linked_at
    (prog : program) (syms : symbols)
    (fn : function) (global_offset : nat) : Prop :=
    forall fn_offset : nat,
      (fn_offset < length (snd fn))%nat ->
      exists i1 i2,
        fetch_fn (fst (fst fn), fn_offset) fn = Some i1
        /\ fetch (global_offset, fn_offset) prog = Some i2
        /\ insn_equiv syms i1 i2.

End Build.

Instance symbols_ok : map.ok symbols := (SortedListString.ok nat).

Section BuildProofs.
  Import ErrorMonadNotations.

  (* Returns the overall size of the program containing the functions
     and starting at the given offset. *)
  Definition program_size (start : nat) (fns : list function) : nat :=
    fold_left
      (fun offset fn =>
         let fn_insns := snd fn in
          (offset + length fn_insns)%nat)
      fns start.

  Ltac err_simpl_step :=
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
  Ltac err_simpl := repeat err_simpl_step.

  Lemma link_symbols'_step :
    forall start_syms start_offset fn fns syms1 syms2 end_offset1 end_offset2,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms1, end_offset1) ->
      link_symbols' syms1 end_offset1 fns = Ok (syms2, end_offset2) ->
      link_symbols' start_syms start_offset (fn :: fns) = Ok (syms2, end_offset2).
  Proof.
    cbv [link_symbols']; intros; cbn [maybe_fold_left bind]; err_simpl; congruence.
  Qed.

  Lemma link_symbols'_offset :
    forall fns start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      end_offset = program_size start_offset fns.
  Proof.
    cbv [link_symbols' program_size]; induction fns; cbn [maybe_fold_left fold_left]; intros;
      err_simpl; [ reflexivity | ].
    destruct_products; cbn [fst snd] in *.
    lazymatch goal with
    | H : link_symbols_for_function _ _ = _ |- _ => cbv [link_symbols_for_function] in H
    end.
    err_simpl; cbn [fst snd] in *. eauto.
  Qed.
  
  Lemma link_symbols'_inv :
    forall start_syms start_offset fn fns syms2 end_offset2,
      link_symbols' start_syms start_offset (fn :: fns) = Ok (syms2, end_offset2) ->
      exists syms1 end_offset1,
        link_symbols_for_function (start_syms, start_offset) fn = Ok (syms1, end_offset1)
        /\ end_offset2 = program_size end_offset1 fns
        /\ link_symbols' syms1 end_offset1 fns = Ok (syms2, end_offset2).
  Proof.
    cbv [link_symbols']; cbn [maybe_fold_left bind]; intros; err_simpl.
    destruct_products; cbn [fst snd] in *.
    repeat lazymatch goal with
           | H : context [link_symbols_for_function ?a ?b]
             |- context [link_symbols_for_function ?a ?b] =>
               destruct (link_symbols_for_function a b) as [[? ?]|]; cbn [bind]
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           | _ => solve [eauto using link_symbols'_offset]
           end.    
  Qed.

  Lemma link_symbols_for_function_size :
    forall fn start_syms start_offset syms size,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, size) ->
      size = (start_offset + length (snd fn))%nat.
  Proof.
    cbv [link_symbols_for_function]; intros; err_simpl; reflexivity.
  Qed.

  Lemma link_symbols'_size :
    forall fns start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      program_size start_offset fns = end_offset.
  Proof.
    cbv [program_size]; induction fns; intros;
      [ cbn [link_symbols' maybe_fold_left] in *; err_simpl; reflexivity | ].
    cbn [fold_left].
    repeat lazymatch goal with
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               eapply link_symbols'_inv in H
           | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
               apply link_symbols_for_function_size in H; subst
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | _ => subst; solve [eauto]
           end.
  Qed.

  Lemma add_symbol_no_overwrite start_syms label1 label_offset1 syms :
    add_symbol start_syms label1 label_offset1 = Ok syms ->
    (forall label2 label_offset2,
        map.get start_syms label2 = Some label_offset2 ->
        map.get syms label2 = Some label_offset2).
  Proof.
    cbv [add_symbol]; intros.
    destr (map.get start_syms label1); [ congruence | ].
    destr (string_dec label1 label2); subst; [ congruence | ].
    err_simpl. rewrite map.get_put_diff by congruence.
    auto.
  Qed.

  Lemma merge_symbols_no_overwrite fn_syms global_offset global_syms :
    forall syms,
      merge_symbols global_offset global_syms fn_syms = Ok syms ->
      (forall label label_offset,
          map.get global_syms label = Some label_offset ->
          map.get syms label = Some label_offset).
  Proof.
    cbv [merge_symbols].
    lazymatch goal with
    | |- forall syms,
        map.fold _ _ _ = ?x -> ?Q =>
        apply (map.fold_spec (fun _ m => forall syms, m = x -> Q))
    end; intros; err_simpl; eauto using add_symbol_no_overwrite.
  Qed.

  Lemma link_symbols_for_function_no_overwrite :
    forall fn start_syms start_offset syms label label_offset end_offset,
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      map.get start_syms label = Some label_offset ->
      map.get syms label = Some label_offset.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function]; cbn [bind fst snd]; intros.
    err_simpl. eauto using add_symbol_no_overwrite, merge_symbols_no_overwrite.
  Qed.

  Lemma link_symbols'_no_overwrite :
    forall fns start_syms start_offset syms label label_offset end_offset,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      map.get start_syms label = Some label_offset ->
      map.get syms label = Some label_offset.
  Proof.
    cbv [program_size]; induction fns; intros;
      [ cbn [link_symbols' maybe_fold_left] in *; err_simpl; solve [auto] | ].
    repeat lazymatch goal with
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               eapply link_symbols'_inv in H
           | H : exists _, _ |- _ => destruct H; subst
           | H : _ /\ _ |- _ => destruct H; subst
           | _ => solve [eauto using link_symbols_for_function_no_overwrite]
           end.
  Qed.

  Lemma add_symbol_correct start_syms label label_offset syms :
      add_symbol start_syms label label_offset = Ok syms ->
      map.get syms label = Some label_offset.
  Proof.
    cbv [add_symbol]; destruct_one_match; intros; err_simpl; auto using map.get_put_same.
  Qed.

  Lemma link_symbols_for_function_correct fn start_syms start_offset syms end_offset :
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some start_offset.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function]; cbn [bind fst snd]; intros; err_simpl.
    eauto using add_symbol_correct, merge_symbols_no_overwrite.    
  Qed.

  Lemma link_symbols'_correct :
    forall fns1 fns2 fn start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some (program_size start_offset fns1).
  Proof.
    cbv [link_symbols program_size]; induction fns1; intros.
    { rewrite ?app_nil_l in *. cbn [link_symbols' maybe_fold_left] in *.
      err_simpl. destruct_products.
      eauto using link_symbols'_no_overwrite, link_symbols_for_function_correct. }
    { rewrite <-?app_comm_cons in *. cbn [fold_left].
      repeat lazymatch goal with
             | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
                 eapply link_symbols'_inv in H
             | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
                 apply link_symbols_for_function_size in H; subst
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => subst; solve [eauto]                                 
             end. }
  Qed.

  Lemma link_cinsn_correct syms i1 i2 : 
    link_cinsn syms i1 = Ok i2 ->
    cinsn_equiv syms i1 i2.
  Proof.
    cbv [link_cinsn cinsn_equiv]; intros.
    destruct_one_match; err_simpl; ssplit; auto;
      lazymatch goal with
      | H : map_err (map.get ?m ?k) _ = Ok _ |- _ =>
          destr (map.get m k); cbn [map_err] in H; err_simpl
      end; reflexivity.
  Qed.

  Lemma link_insn_correct syms i1 i2 : 
    link_insn syms i1 = Ok i2 ->
    insn_equiv syms i1 i2.
  Proof.
    cbv [link_insn insn_equiv]; intros.
    destruct_one_match; err_simpl; eauto using link_cinsn_correct.
  Qed.

  Lemma link_insns_correct :
    forall syms fn_insns prog,
      link_insns syms fn_insns = Ok prog ->
      forall (fn_offset : nat),
        (fn_offset < length fn_insns)%nat ->
        exists i1 i2,
          nth_error fn_insns fn_offset = Some i1
          /\ nth_error prog fn_offset = Some i2
          /\ insn_equiv syms i1 i2.
  Proof.
    induction fn_insns; intros; cbn [link_insns length] in *; err_simpl; [ lia | ].
    destr fn_offset; cbn [nth_error].
    { do 2 eexists; ssplit; try reflexivity; eauto using link_insn_correct. }
    { apply IHfn_insns; auto; lia. }
  Qed.

  Lemma fetch_fn_name offset (fn : function) :
    fetch_fn (fst (fst fn), offset) fn = nth_error (snd fn) offset.
  Proof.
    cbv [fetch_fn get_label_offset]. cbn [fst snd].
    rewrite String.eqb_refl, Nat.add_0_l. reflexivity.
  Qed.

  Lemma linked_at_cons i prog syms fn offset :
    linked_at prog syms fn offset ->
    linked_at (i :: prog) syms fn (S offset).
  Proof.
    cbv [linked_at]; cbn [fst snd]. intro Hlink; intros.
    specialize (Hlink _ ltac:(eassumption)). destruct_products.
    eauto.
  Qed.

  Lemma link'_correct :
    forall start_prog fn prog syms offset,
      link' syms start_prog fn = Ok prog ->
      offset = length start_prog ->
      linked_at prog syms fn offset.
  Proof.
    cbv [link']; induction start_prog; intros; subst.
    { err_simpl. rewrite app_nil_l in *. cbn [length].
      cbv [linked_at]; intros.
      lazymatch goal with H : link_insns _ _ = _ |- _ =>
                            eapply link_insns_correct in H; eauto end.
      destruct_products. cbn [fst snd].
      rewrite fetch_fn_name. cbv [fetch]; cbn [fst snd].
      eauto. }
    { err_simpl. rewrite <-app_comm_cons. cbn [length].
      apply linked_at_cons. apply IHstart_prog; auto; err_simpl.
      reflexivity. }
  Qed.

  Lemma link'_no_unlink :
    forall fn1 fn2 syms offset start_prog prog,
      link' syms start_prog fn2 = Ok prog ->
      linked_at start_prog syms fn1 offset ->
      linked_at prog syms fn1 offset.
  Proof.
    cbv [link']; intros. err_simpl. cbv [linked_at]; intros.
    lazymatch goal with H : linked_at _ _ _ _ |- _ =>
                          specialize (H _ ltac:(eassumption))
    end.
    destruct_products. do 2 eexists; ssplit; eauto; [ ].
    cbv [fetch] in *; cbn [fst snd] in *.
    lazymatch goal with
    | H : nth_error ?l1 ?i = Some _ |- _ =>
        assert (i < length l1)%nat by eauto using List.nth_error_Some_bound_index
    end.
    rewrite nth_error_app1 by lia. auto.
  Qed.

  Lemma fold_link'_no_unlink :
    forall fns fn syms offset start_prog prog,
      maybe_fold_left (link' syms) fns start_prog = Ok prog ->
      linked_at start_prog syms fn offset ->
      linked_at prog syms fn offset.
  Proof.
    induction fns; cbn [maybe_fold_left]; intros; err_simpl;
      eauto using link'_no_unlink.
  Qed.

  Lemma link_insns_length :
    forall syms insns prog,
    link_insns syms insns = Ok prog ->
    length prog = length insns.
  Proof.
    induction insns; cbn [link_insns length]; intros; err_simpl; [ reflexivity | ].
    cbn [length]. rewrite IHinsns; eauto.
  Qed.

  Lemma link'_length syms start_prog fn prog:
    link' syms start_prog fn = Ok prog ->
    length prog = (length start_prog + length (snd fn))%nat.
  Proof.
    cbv [link']. destruct fn as [[fn_name fn_syms] fn_insns]. cbn [fst snd].
    intros; err_simpl. rewrite app_length.
    lazymatch goal with H : link_insns _ _ = _ |- _ => apply link_insns_length in H end.
    lia.
  Qed.

  Lemma link_correct'' :
    forall fns1 fn fns2 start_syms start_offset start_prog syms prog end_offset,
      maybe_fold_left (link' syms) (fns1 ++ fn :: fns2) start_prog = inl prog ->
      link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = inl (syms, end_offset) ->
      start_offset = length start_prog ->
      linked_at prog syms fn (program_size start_offset fns1).
  Proof.
    cbv [program_size]. induction fns1; intros; subst.
    { rewrite app_nil_l in *. cbn [maybe_fold_left fold_left fst snd] in *.
      err_simpl. eauto using link'_correct, fold_link'_no_unlink. }
    { rewrite <-?app_comm_cons in *. cbn [fold_left maybe_fold_left] in *.
      err_simpl.
      repeat lazymatch goal with
             | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
                 eapply link_symbols'_inv in H
             | H: link_symbols_for_function _ _ = Ok _ |- _ =>               
                 apply link_symbols_for_function_size in H; subst
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => progress subst                           
             end.
      eapply IHfns1; eauto; [ ].
      cbv [function] in *; destruct_products; cbn [fst snd] in *.
      lazymatch goal with H : link' _ _ _ = _ |- _ => apply link'_length in H end.
      cbn [fst snd] in *. lia. }
  Qed.

  Lemma link_correct' fns1 fns2 fn prog syms :
      link (fns1 ++ fn :: fns2) = Ok prog ->
      link_symbols (fns1 ++ fn :: fns2) = Ok syms ->
      linked_at prog syms fn (program_size 0%nat fns1).
  Proof.
    cbv [link link_symbols]; intros. err_simpl.
    destruct_products; cbn [fst snd] in *.
    eauto using link_correct''.    
  Qed.

  Lemma link_correct :
    forall fns fn prog syms,
      (* If the function is in the input list of functions `fns`... *)
      In fn fns ->
      (* ...and `prog` is the result of a successful `link`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...then there exists an `offset` and an index `idx`... *)
      exists offset idx,
        (* ...such that `fn` is in the list at index `idx`...  *)
        nth_error fns idx = Some fn
        (* ...and `offset` is the size of the program before `fn`... *)
        /\ offset = program_size 0%nat (firstn idx fns)
        (* ...and `fn` is linked at `offset`. *)
        /\ linked_at prog syms fn offset.
  Proof.
    intros.
    lazymatch goal with H : In _ _ |- _ =>
                          apply in_split in H; destruct H as [fns1 [fns2 ?]]
    end.
    subst. eexists; exists (length fns1); ssplit; [ | reflexivity | ].
    { rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite List.firstn_app_l by lia. eauto using link_correct'. }
  Qed.    

End BuildProofs.

Module Test.
  (* Test program 0 : a function that adds two registers.

     start:
       addi x2, x0, 2
       addi x3, x0, 3
       jal  x1, add
       ecall

     add:
       add  x5, x2, x3
       ret
   *)
  Definition add_fn : function :=
    ("add"%string,
      map.empty,
      [(Add x5 x2 x3 : insn);
       (Ret : insn)]).
  Definition test_program0 : list function :=
    [ ("start",
        map.empty,
        [ (Addi x2 x0 2 : insn);
          (Addi x3 x0 3 : insn);
          (Jal x1 "add" : insn);
          (Ecall : insn)]);
      add_fn ]%string.

  (* Test program 1 : build multiplication out of addition

     mul:
       addi   x4, x0, x0
       loop   x2, 2
         jal    x1, add
         addi   x4, x5, 0
       ret

     add:
       add  x5, x2, x3
       ret
  *)
  Definition test_program1 : list function :=
    [ ("mul",
        map.empty,
        [ (Addi x4 x0 0 : insn);
          (Loop x2 : insn);
          (Jal x1 "add" : insn);
          (Addi x4 x5 0 : insn);
          (LoopEnd : insn);
          (Ret : insn)]);
      add_fn ]%string.

  Compute (link test_program0).
  Compute (link test_program1).

  Ltac derive_blockmap program :=
    let val := eval vm_compute in (build program) in
    lazymatch val with
    | Ok ?x => exact x
    | Err ?e => fail e
    end.

  Definition blocks0 : blockmap := ltac:(derive_blockmap test_program0).
  Definition blocks1 : blockmap := ltac:(derive_blockmap test_program1).

  Ltac solve_map_step t :=
    first [ rewrite map.get_put_diff by t
          | rewrite map.get_put_same by t
          | reflexivity ].
  Ltac solve_map := repeat (solve_map_step ltac:(congruence)).
  Ltac simplify_side_condition_step :=
    lazymatch goal with
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- is_valid_addi_imm _ => cbv [is_valid_addi_imm]; lia
    | |- map.get _ _ = Some _ => solve_map
    | |- (_ < _)%nat => lia
    | |- (_ <= _)%nat => lia
    | |- Some _ = Some _ => reflexivity
    | _ => cbn [run strt1 strt read_gpr write_gpr ctrl1
                  set_pc set_regs call_stack_pop call_stack_push
                  length hd_error tl skipn fst snd
                  repeat_advance_pc advance_pc Z.add Pos.add]
    end.
  Ltac simplify_side_condition := repeat simplify_side_condition_step.

  (* TODO: need to figure out how to do this so it works right if offset goes past end of block *)
  Definition get_block (blocks : map.rep (map:=blockmap)) (pc : Z * nat)
    : option (block Z) :=
    let start := fst pc in
    let offset := snd pc in
    match map.get blocks start with
    | None => None
    | Some (sinsns, final) =>
        if (offset <=? length sinsns)%nat
        then Some (skipn offset sinsns, final)
        else (* TODO: what here? need to go to next block... *)
    end.
    map.get blocks (fst pc + (4 * Z.of_nat (snd pc))).
  Definition get_block (blocks : map.rep (map:=objects)) (pc : string * nat)
    : option (block string) :=
    match map.get blocks fst pc with
    | None => None
    | Some b =>
        
    

  (* problem: returning from a jump you need to break to the next block *)
  (* offset doesn't work here *)
  Print blocks0.
  About run.
  Lemma test_program0_correct (regfile : map.map reg Z) :
    map.ok regfile ->
    eventually
      (run (get_block:=map.get blocks0))
      (fun st =>
         match st with
         | otbn_done _ regs =>
             map.get regs (gpreg x5) = Some 5
         | _ => False
         end)
      (start_state (0, 0%nat)).
  Proof.
    cbv [blocks0 start_state]; intros.
    eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. apply eventually_done.
    solve_map.
  Qed.

  (* Next: prove something about the add block individually, and use
     that to prove something about the mul program individually *)

  (* TODO: maybe need to represent functions with internal labels too?
     for e.g. branches -- may need these blocks to be linked
     sequentially, and it makes loop ends easier too *)
  (* Could also just say "linked at" with size offset *)

  Definition linked_at
    (ctx : blockmap) (fn : function) (pc : Z) :=
    exists program,
      build program = Ok ctx
      /\ In add_fn program
      /\ (let syms := snd (get_symbols program) in
          map.get syms (fst fn) = Some pc).


  (* TODO: can I state the get condition without reimplementing link?
     maybe the get is the same as if I had linked it from 0? *)
  (*
  Lemma linked_at_get ctx fn pc :
    linked_at ctx fn pc ->
    map.get ctx pc = *)
  (* maybe I can talk at the level of objs and syms instead of blockmap? *)
  (* in that case, need:
     - a proof linking reasoning about objs/syms with reasoning about blockmap
     - some way to talk about "running" objs -- technically run just works?

    but what about advance_pc? how can I advance a string?
    could do it with string * offset
    could represent pc and addr differently?
    but then how to do jumps? need extra indirection addr -> Z
    this could work though, then the indirect is map.get syms
    for blockmap it's id
   *)
  Print run_block.
  Print objects.
    

  (* For proofs about the object file, parameterize over the overall program *)
  Lemma add_fn_correct regfile :
    map.ok regfile ->
    forall (ctx : blockmap)
           (regs : regfile) cstack lstack
           start_pc a b,
      linked_at ctx add_fn start_pc ->
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      eventually
        (run_block (advance_pc:=advance_pc) ctx)
        (fun st =>
           match st with
           | otbn_done _ regs' =>
               map.get regs (gpreg x5) = Some (cast32 (a + b))
               /\ map.only_differ regs (PropSet.of_list [gpreg x5]) regs'
           | _ => False
           end)
        (otbn_busy start_pc regs cstack lstack).
  Proof.
    (*
    cbv [linked_at]; intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end. *)
    intros.
    eapply eventually_step.
    { simplify_side_condition.
      Print run_b.

  Qed.


  Check add_fn.
  Print link.
  Check Forall.
  Check get_objects.
  Print objects.
  Compute (get_objects (label_loop_ends test_program1)).
  Compute (get_symbols (label_loop_ends test_program1)).
  Check (fun fn => get_objects (label_loop_ends [fn])).
  Check label_loop_ends.
  Print objects.
  (* given start pc, then for all label, blocks list in objs:
       blockmap[pc + length so far] = block converted to Z
       the "converted to Z" is another prop saying the labels correspond to something in the blockmap?
       maybe we need syms too to state "converted to Z"
   *)
  Definition cinsn_is_linked
    (syms : map.rep (map:=symbols))
    (syms : map.rep (map:=objects))
    (i1 : cinsn (addr:=string))
    (i2 : cinsn (addr:=Z)) : Prop :=
    match i1, i2 with
    | Jal r dst1, Jal r dst2 =>
        map.get syms dst1 = dst2
        /\ 
    | _ => True
    end.
  (* Ugh, this seems a little ugly. Can we do better? *)
  Definition is_linked (blocks : blockmap) (fn : string * list insn) : Prop :=
    let fn := label_loop_ends [fn] in
    let objs := get_objects fn in
    Forall
      (fun label_insns =>
         let label := fst label_insns in
         let insns := snd label_insns in
         map.get label = 
      ) fn.
    map.fold
      (fun P label b =>
         

  
  Definition add_obj : map.rep (map:=objects) := Eval vm_compute in get_objects [add_fn].

  (*
  Print objects.

  (* add zero-offsets to all labels. *)
  Fixpoint init_offsets_cinsn (i : cinsn (addr:=string)) : cinsn (addr:=string * Z) :=
    match i with
    | Ret => Ret
    | Ecall => Ecall
    | Jal r dst => Jal r (dst, 0)
    | Beq r1 r2 dst => Beq r1 r2 (dst, 0)
    | Bne r1 r2 dst => Bne r1 r2 (dst, 0)
    | Loop r n => Loop r n
    | Loopi imm n => Loopi imm n
    end.
  Fixpoint init_offsets_block (b : block string) : block (string * Z) :=
    match snd b with
    | None => (fst b, None)
    | Some i => (fst b, Some (init_offsets_cinsn i))
    end.
  Print objects.
  Print map.map.
  Fixpoint init_offsets (objs : map.rep (map:=objects))
    : map.rep (string * Z) (block (string * Z)) :=
    map.fold
      (fun 
    *)

  Check run_block.
  Print add_fn.
  Eval compute in get_objects [add_fn].
  Print objects.
  (* For proofs about the object file, parameterize over the overall blockmap *)
  Lemma add_fn_correct regfile :
    map.ok regfile ->
    forall (ctx : blockmap) (regs : regfile) add_pc a b,
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      map.get blockmap add_pc = 
      eventually
        (run_block (advance_pc:=advance_pc) ctx)
        (fun st =>
           match st with
           | otbn_done _ regs' =>
               map.get regs (gpreg x5) = Some 5
               /\ map.only_differ regs (PropSet.of_list [gpreg x5]) regs'
           | _ => False
           end)
        (start_state 0).
End Test.
