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
  Inductive cinsn {addr : Type} : Type :=
  (* TODO: technically ret is a special case of JALR, but only RET is used in practice *)
  | Ret : cinsn
  | Ecall : cinsn
  | Jal : gpr -> addr -> cinsn
  | Bne : gpr -> gpr -> addr -> cinsn
  | Beq : gpr -> gpr -> addr -> cinsn
  | Loop : gpr -> nat -> cinsn
  | Loopi : nat -> nat -> cinsn
  .

  Inductive insn {addr : Type} : Type :=
  | Straightline : sinsn -> insn
  | Control : cinsn (addr:=addr) -> insn
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

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

(* Executable model of OTBN. *)
Section Exec.
  (* Parameterize over the representation of code locations. *)
  Context {addr : Type}
    {advance_pc : addr -> addr}
    {addr_eqb : addr -> addr -> bool}
    {addr_eqb_spec : forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (addr_eqb a1 a2)}.
  Definition block (addr : Type) : Type := (list sinsn * option (cinsn (addr:=addr))).

  (* error values for cases that should be unreachable (these can be
     any value and exist mostly to help debugging -- it's easier to
     understand that something went wrong when you see "error_Z" than
     an unexpected 0). *)
  Context {error_Z : Z}.

  (* Parameterize over the map implementation. *)
  Context {regfile : map.map reg Z} {blockmap : map.map addr (block addr)}.

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

  Definition run1
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

  Fixpoint run (regs : regfile) (sinsns : list sinsn) (post : regfile -> Prop) : Prop :=
    match sinsns with
    | [] => post regs
    | i :: sinsns => run1 regs i (fun regs => run regs sinsns post)
    end.

  Fixpoint repeat_advance_pc (pc : addr) (n : nat) : addr :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.

  Local Notation call_stack := (list addr) (only parsing).
  Local Notation loop_stack := (list (addr * addr * nat)) (only parsing).
  Inductive otbn_state : Type :=
  | otbn_busy (pc : addr) (regs : regfile) (cstack : call_stack) (lstack : loop_stack)
  | otbn_error (pc : addr) (errs : list string)
  | otbn_done (pc : addr) (regs : regfile)
  .  
  Definition start_state (start_pc : addr) : otbn_state :=
    otbn_busy start_pc map.empty [] [].
  Definition get_pc (st : otbn_state) : addr :=
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
  Definition set_pc (st : otbn_state) (pc : addr) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy _ regs cstack lstack => post (otbn_busy pc regs cstack lstack)
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
    (st : otbn_state) (iters : nat) (size : nat) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        let start_pc := advance_pc pc in
        let end_pc := repeat_advance_pc pc size in
        (length lstack < 8)%nat
        /\ post (otbn_busy start_pc regs cstack ((start_pc, end_pc, iters) :: lstack))
    | _ => False
    end.

  (* Finish a loop iteration (and potentially the entire loop).
    Expects that the current PC matches the loop-body end PC of the
    first loop stack entry. *)
  Definition loop_end (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists start_addr end_addr iters,
        hd_error lstack = Some (start_addr, end_addr, iters)
        /\ end_addr = pc
        /\ match iters with
           | O => post (otbn_busy (advance_pc pc) regs cstack (tl lstack))
           | S iters =>
               post (otbn_busy start_addr regs cstack
                       ((start_addr, end_addr, iters) :: tl lstack))
           end
    | _ => False
    end.

  (* TODO: is it possible to simplify the address logic here so we can
    directly link "dst" as a block, even if it means repeated terms? *)
  (* TODO: is it necessary to simulate some error conditions? There
     should be a difference between "OTBN had an error", which
     sometimes should in fact happen on some inputs, and "this program
     is not valid" (e.g. out-of-bounds immediate value that cannot be
     encoded). *)
  Definition ctrl1 (st : otbn_state) (i : cinsn) (post : otbn_state -> Prop) : Prop :=
    match i with
    | Ret =>  call_stack_pop st post
    | Ecall => program_exit st post
    | Jal r dst =>
        match r with
        | x0 => set_pc st dst post
        | x1 => call_stack_push st (fun st => set_pc st dst post)
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
                  \/ (v1 <> v2 /\ set_pc st dst post)))
    | Beq r1 r2 dst =>
        read_gpr_from_state st r1
          (fun v1 =>
             read_gpr_from_state st r2
               (fun v2 =>
                  (v1 <> v2 /\ next_pc st post)
                  \/ (v1 = v2 /\ set_pc st dst post)))
    | Loopi v n => loop_start st v n post
    | Loop r n => read_gpr_from_state st r
                    (fun v => 0 < v /\ loop_start st (Z.to_nat v) n post)
    end.

  Definition run_block (blocks : blockmap) (st : otbn_state)
    (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists sinsns final,
        map.get blocks pc = Some (sinsns, final)
        /\ run regs sinsns
             (fun regs =>
                let pc := repeat_advance_pc pc (length sinsns) in
                match final with
                | Some i => ctrl1 st i post
                | None => loop_end st post
                end)
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
 

(* Contains a way to link programs into block maps. *)
Section Build.
  Definition advance_pc (pc : Z) := pc + 4.
  Definition blockmap : map.map Z (block Z) := SortedListZ.map _.
  Definition objects : map.map string (list (block string)) := SortedListString.map _.
  Definition symbols : map.map string Z := SortedListString.map _.
  Import ErrorMonadNotations.

  (* Split a program at a given index in the instruction list and add
     the label. Does nothing if the program is already split at this
     index or the index is past the end of the program. *)
  Fixpoint insert_label
    (program : list (string * list (insn (addr:=string))))
    (idx : nat) (label : string) : list (string * list (insn (addr:=string))) :=
    match program with
    | [] => program
    | fn :: program =>
        let name := fst fn in
        let insns := snd fn in
        if Nat.ltb idx (length insns)
        then if Nat.eqb idx 0
             then program
             else
               let fn1 := (name, firstn idx insns) in
               let fn2 := (label, skipn idx insns) in
               fn1 :: fn2 :: program
        else fn :: insert_label program (idx - length insns) label
    end.

  Definition flatten_program (program : list (string * list (insn (addr:=string))))
    : list (insn (addr:=string)) :=
    fold_left (fun insns fn => insns ++ snd fn) program [].

  (* Go through the program and add labels to the loop ends. *)
  Definition label_loop_ends (program : list (string * list (insn (addr:=string))))
    : list (string * list (insn (addr:=string))) :=
    let insns := flatten_program program in
    snd (fold_left
           (fun lidx_program iidx =>
              let lidx := fst lidx_program in
              let program := snd lidx_program in
              let i := nth_default (Ecall : insn) insns iidx in
              let label := ("loop" ++ String.of_nat lidx ++ "_end")%string in
              match i with
              | Loop _ n =>
                  let program := insert_label program (iidx + 1 + n) label in
                  (S lidx, program)
              | Loopi _ n =>
                  let program := insert_label program (iidx + 1 + n) label in
                  (S lidx, program)
              | _ => (lidx, program)
              end
           )
           (seq 0 (length insns)) (0%nat, program)).

  Fixpoint get_blocks'
    (insns : list (insn (addr:=string)))
    (blocks : list (block string)) (curr : list sinsn)
    : list (block string) :=
    match insns with
    | [] => match curr with
            | [] => blocks
            | _ => blocks ++ [(curr, None)]
            end
    | i :: insns =>
        match i with
        | Straightline i => get_blocks' insns blocks (curr ++ [i])
        | Control i => get_blocks' insns (blocks ++ [(curr, Some i)]) []
        end
    end.
  Definition get_blocks (insns : list (insn (addr:=string))) : list (block string) :=
    get_blocks' insns [] [].

  Definition get_objects (program : list (string * list (insn (addr:=string))))
    : map.rep (map:=objects) :=
    fold_left
      (fun objs fn =>
         let name := fst fn in
         let insns := snd fn in
         map.put objs name (get_blocks insns))
      program map.empty.

  (* Returns the PC at the end of IMEM plus the symbol table. *)
  Definition get_symbols (program : list (string * list (insn (addr:=string)))) 
    : Z * map.rep (map:=symbols) :=
    fold_left
      (fun (pc_syms : Z * (map.rep (map:=symbols))) fn =>
         let pc := fst pc_syms in
         let syms := snd pc_syms in
         let name := fst fn in
         let insns := snd fn in
         let syms := map.put syms name pc in
         let pc := repeat_advance_pc (advance_pc:=advance_pc) pc (length insns) in
         (pc, syms))
      program (0, map.empty).

  Definition link_cinsn
    (syms : map.rep (map:=symbols)) (i : cinsn (addr:=string)) : maybe (cinsn (addr:=Z)) :=
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
    | Loop r n => Ok (Loop r n)
    | Loopi imm n => Ok (Loopi imm n)
    end.

  Definition link_block (syms : map.rep (map:=symbols)) (b : block string) : maybe (block Z) :=
    match snd b with
    | None => Ok (fst b, None)
    | Some i =>
        (i <- link_cinsn syms i;
         Ok (fst b, Some i))
    end.

  Definition block_size {addr} (b : block addr) : nat :=
    length (fst b) + (match snd b with
                      | None => 0
                      | Some _ => 1
                      end).

  Fixpoint link_blocks
    (syms : map.rep (map:=symbols)) (curr_blocks : list (block string))
    (all_blocks : blockmap) (pc : Z) : maybe blockmap :=
    match curr_blocks with
    | [] => Ok all_blocks
    | b :: curr_blocks =>
        (b <- link_block syms b;
         link_blocks syms curr_blocks
           (map.put all_blocks pc b)
           (repeat_advance_pc (advance_pc:=advance_pc) pc (block_size b)))
    end.

  (* TODO: the intermediate symbols won't be found here... maybe symbol + offset? *)
  (* why do we need objs, given the shape program has already? Can we just skip it? *)
  Definition link (objs : map.rep (map:=objects))
    (syms : map.rep (map:=symbols)) : maybe blockmap :=
    map.fold
      (fun all_blocks name curr_blocks =>
         (all_blocks <- all_blocks;
          pc <- map_err (map.get syms name) ("Symbol " ++ name ++ " not found");
          link_blocks syms curr_blocks all_blocks pc))
      (Ok map.empty)
      objs.

  Definition build (program : list (string * list (insn (addr:=string))))
    : maybe blockmap :=
    let program := label_loop_ends program in
    let objs := get_objects program in
    let syms := snd (get_symbols program) in
    link objs syms.
End Build.

Module Test.
  (* TODO: the current method can't reason about individual functions
  at all -- we get a call stack error, no? Maybe we can make proofs
  that include "there's a PC in the call stack"? *)
  
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
  Definition test_program0 : list (string * list (insn (addr:=string))) :=
    [ ("start",
        [ (Addi x2 x0 2 : insn);
          (Addi x3 x0 3 : insn);
          (Jal x1 "add" : insn);
          (Ecall : insn)]);
      ("add",
        [(Add x5 x2 x3 : insn);
         (Ret : insn)])]%string.

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
  Definition test_program1 : list (string * list (insn (addr:=string))) :=
    [ ("mul",
        [ (Addi x4 x0 0 : insn);
          (Loop x2 2 : insn);
          (Jal x1 "add" : insn);
          (Addi x4 x5 0 : insn);
          (Ret : insn)]);
      ("add",
        [(Add x5 x2 x3 : insn);
         (Ret : insn)])]%string.

  Compute (label_loop_ends test_program0).
  Compute (get_objects test_program0).
  Compute (get_symbols test_program0).
  Compute (build test_program0).
  
  Compute (label_loop_ends test_program1).
  Compute (get_objects test_program1).
  Compute (get_symbols test_program1).
  Compute (build test_program1).

  Ltac derive_blockmap program :=
    let val := eval vm_compute in (build program) in
    lazymatch val with
    | inl ?x => exact x
    | inr ?e => fail e
    end.

  Definition blocks0 : blockmap := ltac:(derive_blockmap test_program0).
  Definition blocks1 : blockmap := ltac:(derive_blockmap test_program1).

  Check eventually (run_block blocks0).
  Print otbn_state.
  Lemma test_program0_correct regfile :
    map.ok regfile ->
    forall (regs : regfile) a b,
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      eventually (run_block blocks0) regs
  Proof.
    cbv [test_blk_add]; intros.
    rewrite run_block_step. cbv [run1].
    eexists; split; [ eassumption | ].
    eexists; split; [ eassumption | ].
    cbv [write_gpr].
  Qed.
End Test.
