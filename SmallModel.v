Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Z.PushPullMod.
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
  Definition reg_eqb (r1 r2 : reg) : bool :=
    match r1, r2 with
    | gpreg r1, gpreg r2 => gpr_eqb r1 r2
    | csreg r1, csreg r2 => csr_eqb r1 r2
    | _, _ => false
    end.

  Print BoolSpec.
  Print destr.destr.
  Local Ltac prove_eqb_spec r1 r2 :=
    destruct r1, r2; constructor; congruence.
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
        /\ post (otbn_busy dst regs (tl cstack) lstack)
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
    match iters with
    | O => False (* iters cannot be zero *)
    | S iters =>
        match st with
        | otbn_busy pc regs cstack lstack =>          
            let start_pc := advance_pc pc in
            (length lstack < 8)%nat
            /\ post (otbn_busy start_pc regs cstack ((start_pc, iters) :: lstack))
        | _ => False
        end
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

  (* Functions consist of a name, internal labels (map of string ->
     offset within the function), and a list of instructions. *)
  Definition function : Type := string * symbols * list (insn (destination:=string)).
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
    (fn : function) (pc : string * nat) : option insn :=
    let label := fst pc in
    let offset := snd pc in
    let fn_insns := snd fn in
    match get_label_offset fn label with
    | None => None
    | Some label_offset => nth_error fn_insns (label_offset + offset)
    end.
 
  (* Fetch from a collection of functions. *)
  Definition fetch_ctx
    (fns : list function) (pc : string * nat) : option insn :=
    fold_left
      (fun res fn =>
         match res, fetch_fn fn pc with
         | None, Some i => Some i
         | _,_ => res
         end)
      fns None.

  (* Fetch from a whole program. *)
  Definition fetch
    (prog : program) (pc : nat * nat) : option insn :=
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
        fetch_fn fn (fst (fst fn), fn_offset) = Some i1
        /\ fetch prog (global_offset, fn_offset) = Some i2
        /\ insn_equiv syms i1 i2.

End Build.

Instance symbols_ok : map.ok symbols := (SortedListString.ok nat).

Section BuildProofs.
  Context {regfile : map.map reg Z}.
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
    fetch_fn fn (fst (fst fn), offset) = nth_error (snd fn) offset.
  Proof.
    cbv [fetch_fn get_label_offset]. cbn [fst snd].
    rewrite String.eqb_refl, Nat.add_0_l. reflexivity.
  Qed.
  
  Lemma fetch_fn_sym fn label offset label_offset :
    label <> fst (fst fn) ->
    map.get (snd (fst fn)) label = Some label_offset ->
    fetch_fn fn (label, offset) = nth_error (snd fn) (label_offset + offset).
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [fetch_fn get_label_offset]; cbn [fst snd]; intros.
    destr (label =? fn_name)%string; [ congruence | ].
    destruct_one_match; congruence.
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

  (* Convenience shorthand for defining function specs. *)
  Definition returns
    {destination : Type} {fetch:destination * nat -> option insn}
    (start : destination) regs cstack lstack
    (spec : regfile -> Prop) : Prop :=
    forall ret_pc,
      hd_error cstack = Some ret_pc ->
      eventually
        (run1 (fetch:=fetch))
        (fun st =>
           match st with
           | otbn_busy pc regs' cstack' lstack' =>
               pc = ret_pc
               /\ spec regs'
               /\ cstack' = tl cstack
               /\ lstack' = lstack
           | _ => False
           end)
        (otbn_busy (start, 0%nat) regs cstack lstack).
  Definition exits_with_errors
    {destination : Type} {fetch:destination * nat -> option insn}
    (start : destination) regs cstack lstack
    (spec : destination * nat -> list string -> Prop) : Prop :=
    eventually
      (run1 (fetch:=fetch))
      (fun st =>
         match st with
         | otbn_error pc errs => spec pc errs
         | _ => False
         end)
      (otbn_busy (start, 0%nat) regs cstack lstack).
  Definition exits
    {destination : Type} {fetch: destination * nat -> option insn}
    (start : destination) regs cstack lstack
    (spec : regfile -> Prop) : Prop :=
    eventually
      (run1 (fetch:=fetch))
      (fun st =>
         match st with
         | otbn_done pc regs => spec regs
         | _ => False
         end)
      (otbn_busy (start, 0%nat) regs cstack lstack).

  (* TODO: have a case for error as well. Maybe just require multiple
  proofs if you want to say something about the error case. *)

  Fixpoint link_call_stack
    (syms : symbols) (cstack : list (string * nat))
    (post : list (nat * nat) -> Prop) : Prop :=
    match cstack with
    | [] => post []
    | (name, local_offset) :: cstack =>
        exists global_offset,
        map.get syms name = Some global_offset
        /\ link_call_stack syms cstack
             (fun cstack => post ((global_offset,local_offset) :: cstack))
    end.

  Fixpoint link_loop_stack
    (syms : symbols) (lstack : list (string * nat * nat))
    (post : list (nat * nat * nat) -> Prop) : Prop :=
    match lstack with
    | [] => post []
    | (name, local_offset, iters) :: lstack =>
        exists global_offset,
        map.get syms name = Some global_offset
        /\ link_loop_stack syms lstack
             (fun lstack => post ((global_offset,local_offset, iters) :: lstack))
    end.

  Definition link_state
    (syms : symbols) (st : otbn_state (destination:=string))
    (spec : otbn_state (destination:=nat) -> Prop)
    : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists offset,
        map.get syms (fst pc) = Some offset
        /\ link_call_stack syms cstack
             (fun cstack =>
                link_loop_stack syms lstack
                  (fun lstack =>
                     spec (otbn_busy (offset, snd pc) regs cstack lstack)))
    | otbn_done pc regs =>
        exists offset,
        map.get syms (fst pc) = Some offset
        /\ spec (otbn_done (offset, snd pc) regs)
    | otbn_error pc errs =>
        exists offset,
        map.get syms (fst pc) = Some offset
        /\ spec (otbn_error (offset, snd pc) errs)
    end.

  Definition link_spec
    (syms : symbols)
    (spec1 : otbn_state (destination:=string) -> Prop)
    (spec2 : otbn_state (destination:=nat) -> Prop) : Prop :=
    forall st, spec1 st -> link_state syms st spec2.

  (* Theorem that connects run1 with a ctx to run1 with a program *)
  Lemma link_run1 :
    forall ctx fns prog syms start_fn start_name start_pc pre_ctx post_ctx,
      (* if all functions from the context are in the input list `fns`... *)
      incl ctx fns ->
      (* ...and `prog` is the result of a successful `link fns`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...and the starting function is linked at `start_pc` ... *)
      linked_at prog syms start_fn start_pc ->
      (* ...and `start_name is the name of the starting function... *)
      start_name = fst (fst start_fn) ->
      (* ...and evaluating the context satisfies the spec for certain states... *)
      (forall st,
          pre_ctx st ->
          eventually (run1 (fetch:=fetch_ctx ctx)) post_ctx st) ->
      (* ...then for all linked-program pre- and post-conditions... *)
      (forall pre_prog post_prog,
          (* ...if the preconditions are related... *)
          link_spec syms pre_ctx pre_prog ->
          (* ...and the preconditions are related... *)
          link_spec syms post_ctx post_prog ->
          (* ...then for all states satisfying the precondition... *)
          forall st,
            pre_prog st ->
            (* ...the program satisfies the spec. *)
            eventually (run1 (fetch:=fetch prog)) post_prog st).
  Proof.
    (* TODO *)
  Admitted.
End BuildProofs.

Module map.
  Section __.
    Context {K V : Type} {map : map.map K V} {map_ok : map.ok map}.
    Context {key_eqb : K -> K -> bool}
      {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

    Lemma only_differ_trans (m1 m2 m3 : map.rep (map:=map)) (s1 s2 s3 : PropSet.set K) :
      map.only_differ m1 s1 m2 ->
      map.only_differ m2 s2 m3 ->
      PropSet.subset (PropSet.union s1 s2) s3 ->
      map.only_differ m1 s3 m3.
    Proof using Type.
      intros. intro k.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : map.only_differ _ _ _ |- _ => specialize (H k)
             | H : PropSet.elem_of _ ?s,
                 H' : PropSet.subset (PropSet.union _ ?s) ?s'
               |- PropSet.elem_of _ ?s' \/ _ =>
                 left; apply H'; apply PropSet.in_union_r; assumption
             | H : PropSet.elem_of _ ?s,
                 H' : PropSet.subset (PropSet.union ?s _) ?s'
               |- PropSet.elem_of _ ?s' \/ _ =>
                 left; apply H'; apply PropSet.in_union_l; assumption
             | H : ?a = ?b, H' : ?b = ?c |- _ \/ ?a = ?c => right; congruence
             end.
    Qed.

    Lemma only_differ_put (m : map.rep (map:=map)) k v s :
      PropSet.subset (PropSet.singleton_set k) s ->
      map.only_differ m s (map.put m k v).
    Proof using map_ok key_eqb_spec.
      intros. cbv [map.only_differ PropSet.elem_of PropSet.subset PropSet.singleton_set] in *.
      intro k'. destr (key_eqb k k'); [ left; solve [auto] | right ].
      rewrite map.get_put_diff; congruence.
    Qed.
  End __.
End map.

Ltac solve_map_step t :=
  first [ rewrite map.get_put_diff by t
        | rewrite map.get_put_same by t                       
        | reflexivity
        | eassumption
        | lazymatch goal with m := _ : map.rep |- _ =>
                                lazymatch goal with |- context [m] => subst m end end
    ].
Ltac solve_map := repeat (solve_map_step ltac:(congruence)).

(* Helper lemmas for proving things about programs. *)
Section Helpers.
  Context {regfile : map.map reg Z}
    {regfile_ok : map.ok regfile}.

  Lemma read_gpr_weaken regs r (P Q : Z -> Prop) :
    read_gpr regs r P ->
    (forall v, P v -> Q v) ->
    read_gpr regs r Q.
  Proof.
    cbv [read_gpr]; intros.
    destruct_one_match; destruct_products; eauto.
  Qed.
  
  Lemma fetch_weaken_run1
    {destination : Type}
    {fetch1 : destination * nat -> option insn}
    {fetch2 : destination * nat -> option insn} :
    forall st P,
      run1 (fetch:=fetch1) st P ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      run1 (fetch:=fetch2) st P.
  Proof.
    induction st; cbn [run1]; intros; auto; [ ].
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end.
    eauto.
  Qed.

  Lemma fetch_weaken
    {destination : Type}
    {fetch1 : destination * nat -> option insn}
    {fetch2 : destination * nat -> option insn} :
    forall st P,
      eventually (run1 (fetch:=fetch1)) P st ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      eventually (run1 (fetch:=fetch2)) P st.
  Proof.
    induction 1; intros; [ auto using eventually_done | ].
    eapply eventually_step; eauto using fetch_weaken_run1.
  Qed.

  Lemma fetch_ctx_done :
    forall fns dst i,
      fold_left (fun res fn =>
                   match res, fetch_fn fn dst with
                   | None, Some i => Some i
                   | _, _ => res
                   end) fns (Some i) = Some i.
  Proof.
    induction fns; cbn [fold_left]; [ reflexivity | ].
    intros. apply IHfns.
  Qed.

  Definition function_symbols_disjoint (fn1 fn2 : function) : Prop :=
    let name1 := fst (fst fn1) in
    let name2 := fst (fst fn2) in
    let syms1 := snd (fst fn1) in
    let syms2 := snd (fst fn2) in
    map.disjoint syms1 syms2
    /\ map.get syms1 name2 = None
    /\ map.get syms2 name1 = None
    /\ name1 <> name2.    

  Lemma fetch_fn_disjoint fn1 fn2 dst i :
    fetch_fn fn1 dst = Some i ->
    function_symbols_disjoint fn1 fn2 ->
    fetch_fn fn2 dst = None.
  Proof.
    cbv [function_symbols_disjoint].
    destruct fn1 as [[name1 syms1] insns1].
    destruct fn2 as [[name2 syms2] insns2].
    destruct dst as [dst offset].
    cbv [fetch_fn get_label_offset]. cbn [fst snd].
    repeat lazymatch goal with
           | |- context [String.eqb ?x ?y] => destr (String.eqb x y); subst; try congruence
           | |- context [match _ with _ => _ end] => destruct_one_match; try congruence
           | H0 : map.disjoint ?m1 ?m2,
               H1 : map.get ?m1 ?k = Some _,
                 H2 : map.get ?m2 ?k = Some _ |- _ =>
               exfalso; eapply H0; eauto
           | H : _ /\ _ |- _ => destruct H
           | H : ?x <> ?x |- _ => congruence
           | H : Some _ = None |- _ => congruence
           | _ => progress intros
           end.
  Qed.

  Lemma fetch_ctx_singleton_iff fn dst i :
    fetch_ctx [fn] dst = Some i <-> fetch_fn fn dst = Some i.
  Proof.
    cbn [fetch_ctx fold_left]. destruct_one_match; split; congruence.
  Qed.

  Lemma fetch_ctx_weaken_cons_eq fns fn dst i :
      fetch_ctx [fn] dst = Some i ->
      fetch_ctx (fn :: fns) dst = Some i.
  Proof.
    cbn [fetch_ctx fold_left]; intro Hfn.
    rewrite Hfn. eauto using fetch_ctx_done.
  Qed.

  (* TODO: rework this lemma so it's easier -- not just fetch_fn =
     None, but fn is disjoint from the symbol table *)
  Lemma fetch_ctx_weaken_cons_ne fns fn dst :
    fetch_fn fn dst = None ->
    fetch_ctx (fn :: fns) dst = fetch_ctx fns dst.
  Proof.
    cbn [fetch_ctx fetch_fn fold_left]; intro Hfn.
    rewrite Hfn. eauto.
  Qed.

  Lemma eventually_jump
    {destination : Type}
    {fetch1 : destination * nat -> option insn}
    {fetch2 : destination * nat -> option insn} :
    forall dst pc (regs : regfile) cstack lstack spec post,
      fetch2 pc = Some (Control (Jal x1 dst)) ->
      (length cstack < 8)%nat ->
      returns (fetch:=fetch1) dst regs (advance_pc pc :: cstack) lstack spec ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      (forall regs,
          spec regs ->
          eventually (run1 (fetch:=fetch2))
            post (otbn_busy (advance_pc pc) regs cstack lstack)) ->
      eventually (run1 (fetch:=fetch2)) post (otbn_busy pc regs cstack lstack).
  Proof.
    cbv [returns]; intros.
    cbn [hd_error] in *.
    eapply eventually_step.
    { cbv [run1]; intros. eexists; split; [ eassumption | ].
      cbv iota. cbn [ctrl1 call_stack_push set_pc].
      ssplit; [ lia .. | ]. apply eq_refl. }
    intros; subst.
    eapply eventually_trans;
      [ eapply fetch_weaken; eauto | intro st; destruct st; try contradiction ].
    intros; repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end. subst.
    cbn [tl]. eauto.
  Qed.
    
  Lemma eventually_invariant {destination : Type} {fetch : destination * nat -> option insn} :
    forall (invariant : nat -> otbn_state -> Prop) iters post st,
      invariant iters st ->
      (forall i st,
          (0 <= i < iters)%nat ->
          invariant (S i) st ->
          eventually (run1 (fetch:=fetch)) (fun st => invariant i st \/ post st) st) ->
      (forall st, invariant 0%nat st -> eventually (run1 (fetch:=fetch)) post st) ->
      eventually (run1 (fetch:=fetch)) post st.
  Proof.
    induction iters; intros; [ solve [eauto] | ].
    apply (eventually_trans _ (fun st => invariant iters st \/ post st));
      repeat match goal with
        | H : _ \/ _ |- _ => destruct H
        | H : context [invariant] |- _ => apply H; auto; lia
        | _ => eapply IHiters; eauto; [ ]
        | _ => progress intros
        | _ => eauto using eventually_done
        end.
  Qed.

  Definition get_lstack {destination : Type} (st : otbn_state)
    : option (list (destination * nat * nat)) :=
    match st with
    | otbn_busy _ _ _ lstack => Some lstack
    | _ => None
    end.

  (* Loop invariant helper lemma. Note: `invariant i` should hold on
     the state the loop has when it reaches the end of the loop body
     in the `i`th iteration from last, so e.g. `invariant 0` should
     hold at the very end of the loop. *)
  Lemma loop_invariant
    {destination : Type} {fetch : destination * nat -> option insn} :
    forall (invariant : nat -> regfile -> Prop)
           (end_pc : destination * nat)
           iters pc r v (regs : regfile) cstack lstack post,
      fetch pc = Some (Control (Loop r)) ->
      fetch end_pc = Some (Control LoopEnd) ->
      read_gpr regs r (eq v) ->
      Z.of_nat iters = v ->
      (length lstack < 8)%nat ->
      iters <> 0%nat ->
      invariant iters regs ->
      (* invariant step condition; if `invariant` holds at start, we reach end *)
      (forall i regs,
          (0 <= i <= iters)%nat ->
          invariant (S i) regs ->
          eventually (run1 (fetch:=fetch))
          (fun st => (exists regs,
                         invariant i regs
                         /\ st = match i with
                                 | S i => otbn_busy (advance_pc pc) regs cstack
                                            ((advance_pc pc, i) :: lstack)
                                 | O => otbn_busy (advance_pc end_pc) regs cstack lstack
                                 end)
                     \/ post st)
            (otbn_busy (advance_pc pc) regs cstack ((advance_pc pc, i) :: lstack))) ->
      (forall regs,
          invariant 0%nat regs ->
          eventually (run1 (fetch:=fetch)) post
            (otbn_busy (advance_pc end_pc) regs cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs cstack lstack).
  Proof.
    cbv [loop_start]; intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct iters; [ lia | ].      
    eapply eventually_step.
    { cbn [run1]. eexists; ssplit; [ eassumption | ].
      cbv iota. cbn [ctrl1 read_gpr_from_state].
      eapply read_gpr_weaken; [ eassumption | ].
      intros; cbv [loop_start]. ssplit; [ lia .. | ].
      subst. rewrite Nat2Z.id.
      ssplit; [ lia .. | ]. eapply eq_refl. }
    intros; subst.
    eapply eventually_invariant
      with (iters := S iters)
           (invariant :=
              fun i st =>
                (exists regs,
                    invariant i regs
                    /\ st = match i with
                            | S i => otbn_busy (advance_pc pc) regs cstack
                                       ((advance_pc pc, i) :: lstack)
                            | O => otbn_busy (advance_pc end_pc) regs cstack lstack
                            end)).
    { intros. subst. eexists; ssplit; eauto. }
    { intros. subst.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | H : context [eventually run1 (fun st => _ \/ post st)] |- _ =>
                 apply H; eauto; lia
             | _ => progress subst
             end. }
    { intros. subst.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | _ => progress subst
             end.
      eauto. }
  Qed.

  Lemma eventually_beq {destination : Type} {fetch : destination * nat -> option insn}:
    forall pc dst r1 r2 regs cstack lstack v1 v2 post,
      fetch pc = Some (Control (Beq r1 r2 dst)) -> 
      read_gpr regs r1 (eq v1) ->
      read_gpr regs r2 (eq v2) ->
      (* branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post (otbn_busy (dst, 0%nat) regs cstack lstack)) ->
      (* no-branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post (otbn_busy (advance_pc pc) regs cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs cstack lstack).
  Proof.
    intros.
    destr (v1 =? v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        cbv [next_pc]. right; ssplit; [ reflexivity | ]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        cbv [next_pc]. left; ssplit; [ congruence | ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_bne {destination : Type} {fetch : destination * nat -> option insn}:
    forall pc dst r1 r2 regs cstack lstack v1 v2 post,
      fetch pc = Some (Control (Bne r1 r2 dst)) -> 
      read_gpr regs r1 (eq v1) ->
      read_gpr regs r2 (eq v2) ->
      (* branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post (otbn_busy (dst, 0%nat) regs cstack lstack)) ->
      (* no-branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post (otbn_busy (advance_pc pc) regs cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs cstack lstack).
  Proof.
    intros.
    destr (v1 =? v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        cbv [next_pc]. left; ssplit; [ reflexivity | ]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        cbv [next_pc]. right; ssplit; [ congruence | ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_loop_end {destination : Type} {fetch : destination * nat -> option insn}:
    forall pc regs cstack lstack loop_start iters post,
      fetch pc = Some (Control LoopEnd) ->
      (match iters with
       | O => eventually (run1 (fetch:=fetch)) post
                (otbn_busy (advance_pc pc) regs cstack lstack)
       | S iters => eventually (run1 (fetch:=fetch)) post
                      (otbn_busy loop_start regs cstack ((loop_start, iters) :: lstack))
       end) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs cstack ((loop_start, iters) :: lstack)).
  Proof.
    intros. destruct iters.
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbn [loop_end hd_error tl ctrl1].
        do 2 eexists; ssplit; [ reflexivity .. | ].
        cbv iota. apply eq_refl. }
      intros; subst. eassumption. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbn [loop_end hd_error tl ctrl1].
        do 2 eexists; ssplit; [ reflexivity .. | ].
        cbv iota. apply eq_refl. }
      intros; subst. eassumption. }
  Qed.

  Lemma cast32_mod x : cast32 x = x mod 2^32.
  Proof. cbv [cast32]. rewrite Z.land_ones; lia. Qed.

End Helpers.

Ltac simplify_cast_step :=
  lazymatch goal with
  | |- context [cast32 ?x] => rewrite !cast32_mod
  | |- context [_ + 0] => rewrite Z.add_0_r
  | |- context [0 + _] => rewrite Z.add_0_l
  | |- context [_ - 0] => rewrite Z.sub_0_r
  | |- context [?x - ?x] => rewrite Z.sub_diag
  | |- context [_ * 0] => rewrite Z.mul_0_r
  | |- context [0 * _] => rewrite Z.mul_0_l
  | |- context [_ * 1] => rewrite Z.mul_1_r
  | |- context [1 * _] => rewrite Z.mul_1_l
  | |- context [0 mod _] => rewrite Z.mod_0_l by lia
  | |- context [Z.of_nat (Z.to_nat _)] => rewrite Z2Nat.id by lia
  | |- context [Z.to_nat (Z.of_nat _)] => rewrite Nat2Z.id by lia
  | |- context [Z.of_nat 0] => change (Z.of_nat 0) with 0
  | |- context [Z.of_nat 1] => change (Z.of_nat 1) with 1
  | _ => progress Z.push_pull_mod
  end.
Ltac simplify_cast := repeat simplify_cast_step.

Ltac simplify_side_condition_step :=
  match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- is_valid_addi_imm _ => cbv [is_valid_addi_imm]; lia
  | |- context [(_ + 0)%nat] => rewrite Nat.add_0_r
  | |- context [fetch_fn (?s, _, _) (?s, _)] => rewrite fetch_fn_name by auto
  | |- context [fetch_fn _ _] =>
      erewrite fetch_fn_sym by
      (cbn [fst snd]; first [ congruence | solve_map ])
  | |- map.get _ _ = Some _ => solve_map
  | |- context [advance_pc (?dst, ?off)] =>
      change (advance_pc (dst, off)) with (dst, S off)
  | |- (_ < _) => lia
  | |- (_ <= _) => lia                                   
  | |- (_ < _)%nat => lia
  | |- (_ <= _)%nat => lia
  | |- Some _ = Some _ => reflexivity
  | _ => first [ progress
                   cbn [run1 strt1 read_gpr write_gpr ctrl1
                          read_gpr_from_state
                          set_pc set_regs call_stack_pop call_stack_push
                          length hd_error tl skipn nth_error fold_left
                          fetch fetch_ctx Nat.add fst snd
                          repeat_advance_pc advance_pc]
               | eassumption ]
  end.
Ltac simplify_side_condition := repeat simplify_side_condition_step.

Module Test.
  Context {regfile : map.map reg Z}
    {regfile_ok : map.ok regfile}.
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
  Definition start_fn : function :=
    ("start",
      map.empty,
      [ (Addi x2 x0 2 : insn);
        (Addi x3 x0 3 : insn);
        (Jal x1 "add" : insn);
        (Ecall : insn)])%string.

  Compute (link [start_fn; add_fn]).

  (* Test program 1 : build multiplication out of addition

     mul:
       addi   x2, x0, x0
       beq    x4, x0, _mul_end
       loop   x4, 2
         jal    x1, add
         addi   x2, x5, 0
       _mul_end:
       ret

     add:
       add  x5, x2, x3
       ret
   *)
  Definition mul_fn : function :=
    Eval cbn [List.app length] in (
        let syms := map.empty in
        let body : list insn :=
          [ (Addi x2 x0 0 : insn);
            (Beq x4 x0 "_mul_end" : insn);
            (Loop x4 : insn);
            (Jal x1 "add" : insn);
            (Addi x2 x5 0 : insn);
            (LoopEnd : insn)] in
        let syms := map.put syms "_mul_end" (length body) in
        let body := (body ++  [(Ret : insn)])%list in
        ("mul", syms, body))%string.

  Compute (link [mul_fn; add_fn]).

  Ltac link_program fns :=
    let val := eval vm_compute in (link fns) in
    lazymatch val with
    | inl ?x => exact x
    | inr ?e => fail e
    end.

  Definition prog0 : program := ltac:(link_program [start_fn; add_fn]).

  Lemma prog0_correct :
    eventually
      (run1 (fetch:=fetch prog0))
      (fun st =>
         match st with
         | otbn_done _ regs =>
             map.get regs (gpreg x5) = Some 5
         | _ => False
         end)
      (start_state (0%nat, 0%nat)).
  Proof.
    cbv [prog0 start_state]; intros.
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
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_done.
    solve_map.
  Qed.

  Lemma add_correct :
    forall regs cstack lstack a b,
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      returns
        (fetch:=fetch_ctx [add_fn])
        "add"%string regs cstack lstack
        (fun regs' =>
           regs' = map.put regs (gpreg x5) (cast32 (a + b))).
  Proof.
    cbv [add_fn returns].
    intros; subst. eapply eventually_step.
    { simplify_side_condition. eapply eq_refl. }
    intros; subst. eapply eventually_step.
    { simplify_side_condition; cbv [advance_pc];
      simplify_side_condition. eapply eq_refl. }
    intros; subst. eapply eventually_done.
    ssplit; reflexivity.
  Qed.

  Ltac get_next_insn :=
    lazymatch goal with
    | |- eventually (@run1 _ _ ?fetch) _ (otbn_busy ?pc _ _ _) =>
        let i := eval vm_compute in (fetch pc) in
          i
    end.

  (* Debugging tactic, prints the next instruction to be fetched. *)
  Ltac print_next_insn :=
    let i := ltac:(get_next_insn) in
    idtac i.

  (* Finds the PC that matches the end of the loop. *)
  Ltac find_loop_end' fetch pc :=
    let i := eval vm_compute in (fetch pc) in
      match i with
      | Some (Control LoopEnd) => pc
      | Some (Control (Loop _)) =>
          let end_pc := find_loop_end' fetch (advance_pc pc) in
          find_loop_end' fetch (advance_pc end_pc)
      | Some (Control (Loopi _)) =>
          let end_pc := find_loop_end' fetch (advance_pc pc) in
          find_loop_end' fetch (advance_pc end_pc)
      | Some _ => find_loop_end' fetch (advance_pc pc)
      | None => fail "reached end of function without finding loop end"
      end.
  Ltac find_loop_end :=
    lazymatch goal with
    | |- context [eventually (@run1 _ _ ?fetch) _ (otbn_busy ?pc _ _ _)] =>
        let i := eval vm_compute in (fetch pc) in
          match i with
          | Some (Control (Loop _)) => find_loop_end' fetch (advance_pc pc)
          | Some (Control (Loopi _)) => find_loop_end' fetch (advance_pc pc)
          | ?x => fail "expected a loop insn at " pc ", got " x
          end
    | _ => fail "could not determine fetch and pc from goal"
    end.

  Ltac remember_registers := 
    lazymatch goal with
    | |- ?P (otbn_busy _ (map.put ?regs ?k ?v) _ _) =>
        let v' := fresh "v" in
        let regs' := fresh "regs" in
        set (v':= v);
        set (regs':=map.put regs k v')
    end.
  Ltac straightline_step :=
    let i := get_next_insn in
    lazymatch i with
    | Some (Straightline _) =>
        intros; subst; eapply eventually_step;
        [ simplify_side_condition; [ .. | simplify_cast; try eapply eq_refl]
        | intros; subst; try remember_registers ]
    | Some ?i => fail "next instruction is not straightline:" i
    | None => fail "pc is invalid?"
    end.

  Ltac subst_lets_step :=
    multimatch goal with
    | x := _ |- _ => lazymatch goal with |- context [x] => subst x end
    end.
  Ltac subst_lets := repeat subst_lets_step.

  Lemma mul_correct :
    forall regs cstack lstack a b,
      map.get regs (gpreg x3) = Some a ->
      map.get regs (gpreg x4) = Some b ->
      0 <= a ->
      0 <= b ->
      (length cstack < 8)%nat ->
      (length lstack < 8)%nat ->
      returns
        (fetch:=fetch_ctx [mul_fn; add_fn])
        "mul"%string regs cstack lstack
        (fun regs' =>
           map.get regs' (gpreg x2) = Some (cast32 (a * b))
           /\ map.only_differ regs (PropSet.of_list [gpreg x2; gpreg x5]) regs').
  Proof.
    cbv [mul_fn returns]. intros; subst.
    repeat straightline_step.
 
    (* branch; use branch helper lemma *)
    eapply eventually_beq.
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { simplify_side_condition; reflexivity. }
    { (* case: b = 0, exit early *)
      intros; subst. eapply eventually_step.
      { simplify_side_condition. apply eq_refl. }
      intros; subst. eapply eventually_done.
      simplify_cast.
      ssplit; try reflexivity; [ solve_map; reflexivity | ].
      (* only_differ clause *)
      eapply map.only_differ_put.
      cbv [PropSet.singleton_set PropSet.subset PropSet.of_list PropSet.elem_of In].
      intros; subst. tauto. }
    (* case: b <> 0, proceed *)
    intros; subst.

    (* loop; use loop invariant lemma *)
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' =>
           map.get regs' (gpreg x2) = Some (cast32 (a * (b - Z.of_nat i)))
           /\ map.only_differ regs (PropSet.of_list [gpreg x2; gpreg x5]) regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; [ | ].
      { simplify_side_condition. simplify_cast. reflexivity. }
      { simplify_side_condition. cbv [map.only_differ]. intro r.
        destr (reg_eqb r (gpreg x2)); [ left | right; solve_map ].
        cbn [PropSet.elem_of PropSet.of_list In]. tauto. } }
    { (* invariant step; proceed through loop and prove invariant still holds *)
      intros; subst. repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.

      (* helper assertion that mul and add don't share symbols *)
      assert (function_symbols_disjoint add_fn mul_fn).
      { cbv [function_symbols_disjoint]; cbn [add_fn mul_fn fst snd].
        ssplit; solve_map; try congruence; [ ].
        cbv [map.disjoint]; intros *. rewrite map.get_empty; congruence. }

      (* jump to "add" function *)
      eapply eventually_jump.
      { reflexivity. }
      { lia. }
      { apply add_correct; eauto; [ ].
        lazymatch goal with H : map.only_differ _ _ ?regs |- context [map.get ?regs ?k]=>
                              let H' := fresh in
                              destruct (H k) as [? | H']; [ | rewrite <-H'; eauto ] end.
        cbn [PropSet.elem_of PropSet.of_list In] in *.
        repeat lazymatch goal with
               | H : _ \/ _ |- _ => destruct H; try congruence; try contradiction
               end. }
      { intros.
        rewrite fetch_ctx_weaken_cons_ne; [ eassumption | ].
        eapply fetch_fn_disjoint; eauto; [ ].
        eapply fetch_ctx_singleton_iff; eauto. }

      (* post-jump; continue *)
      cbv beta. intros; subst.
      repeat straightline_step.

      (* end of loop; use loop-end helper lemma *)
      eapply eventually_loop_end; [ reflexivity .. | ].
      destruct_one_match.
      { (* case: i = 0, loop ends *)
        intros; subst. eapply eventually_done.
        left. eexists; ssplit; [ .. | reflexivity ]; solve_map.        
        { simplify_side_condition. subst_lets. simplify_cast.
          repeat (f_equal; try lia). }
        { simplify_side_condition.
          repeat lazymatch goal with
                 | H : map.only_differ ?m1 _ ?m2 |- map.only_differ ?m1 _ ?m2 => apply H 
                 | |- map.only_differ _ _ (map.put _ _ _) =>
                     eapply map.only_differ_trans; [ | eapply map.only_differ_put | ]
                 | |- PropSet.subset _ _ => reflexivity
                 end; [ ].
          cbv [PropSet.subset PropSet.union PropSet.of_list In PropSet.elem_of
                 PropSet.singleton_set]. tauto. } }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        left. eexists; ssplit; [ .. | reflexivity ]; solve_map.
        { simplify_side_condition. subst_lets; simplify_cast.
          repeat (f_equal; try lia). }
        { simplify_side_condition.
          repeat lazymatch goal with
                 | H : map.only_differ ?m1 _ ?m2 |- map.only_differ ?m1 _ ?m2 => apply H 
                 | |- map.only_differ _ _ (map.put _ _ _) =>
                     eapply map.only_differ_trans; [ | eapply map.only_differ_put | ]
                 | |- PropSet.subset _ _ => reflexivity
                 end; [ ].
          cbv [PropSet.subset PropSet.union PropSet.of_list In PropSet.elem_of
                 PropSet.singleton_set]. tauto. } } }
 
    (* invariant implies postcondition (i.e. post-loop code) *)
    rewrite Z.sub_0_r; intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           end.
    simplify_side_condition.
    repeat straightline_step.
    intros; subst. eapply eventually_step.
    { simplify_side_condition. eapply eq_refl. }
    intros; subst. eapply eventually_done.
    ssplit; eauto.
  Qed.

  (* Test scaling with a large codegen. *)
  Definition repeat_add (n : nat) : function :=
    (("add" ++ String.of_nat n)%string,
      map.empty,
      (Addi x2 x0 0 : insn) :: repeat (Add x2 x2 x3 : insn) n ++ [(Ret : insn)]).
  Definition add100 : function := Eval vm_compute in (repeat_add 100).

  Lemma add100_correct :
    forall regs cstack lstack a,
      map.get regs (gpreg x3) = Some a ->
      0 <= a ->
      returns
        (fetch:=fetch_ctx [add100])
        "add100"%string regs cstack lstack
        (fun regs' =>
           map.get regs' (gpreg x2) = Some (cast32 (a * 100))
           /\ map.only_differ regs (PropSet.of_list [gpreg x2]) regs').
  Proof.
    cbv [add100 returns]; intros.
    straightline_step.
    (* almost all the time here is currently taken in solving the map
       to get the value of x3, which requires substing all the
       map-lets since the beginning because x3 doesn't change *)
    (* can we do this better? instead of map.put, maybe we have a new
       map such that x2 = new value and otherwise no changes *)
    (* maybe we always have a state such that we forget everything except:
       - the values of live registers
       - the only_differ from the original state *)
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step. (* 28.6s *)
    
    intros; subst. eapply eventually_step.
    { simplify_side_condition. eapply eq_refl. }
    intros; subst. eapply eventually_done.
    simplify_cast.
    ssplit; try reflexivity; [ | ].
    { solve_map. subst_lets. simplify_cast.
      f_equal. f_equal. lia. }
    { (* only_differ clause *)
      solve_map.
      repeat lazymatch goal with
             | |- map.only_differ ?m _ (map.put ?m _ _) =>
                 eapply map.only_differ_put
             | H : map.only_differ ?m1 _ ?m2 |- map.only_differ ?m1 _ ?m2 => apply H 
             | |- map.only_differ _ _ (map.put _ _ _) =>
                 eapply map.only_differ_trans; [ | eapply map.only_differ_put | ]
             | |- PropSet.subset _ _ => reflexivity
             end; [ ].
      cbv. tauto. }
  Time Qed.

  
  (* Next: try to apply link_run1, then try to prove it if form is OK *)
  (* Next: try to add more realistic error conditions for e.g. loop errors *)

End Test.
