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
  (* Note: loops here use an end instruction instead of an iteration
     count to make codegen and processing easier. *)
  | Loop : gpr -> cinsn
  | Loopi : nat -> cinsn
  | LoopEnd : cinsn
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

Section Stringify.
  Context {addr : Type} {addr_to_string : addr -> string}.
  Local Coercion addr_to_string : addr >-> string.

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

  Definition cinsn_to_string (i : cinsn (addr:=addr)) : string :=
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
  (* Parameterize over the representation of code locations. *)
  Context {addr : Type}
    {addr_eqb : addr -> addr -> bool}
    {addr_eqb_spec : forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (addr_eqb a1 a2)}.
  Definition block (addr : Type) : Type := (list sinsn * cinsn (addr:=addr)).
  Definition advance_pc (pc : addr * nat) := (fst pc, S (snd pc)).

  (* error values for cases that should be unreachable (these can be
     any value and exist mostly to help debugging -- it's easier to
     understand that something went wrong when you see "error_Z" than
     an unexpected 0). *)
  Context {error_Z : Z}.

  (* Parameterize over the map implementation. *)
  Context {regfile : map.map reg Z} {get_block : addr * nat -> option (block addr)}.

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

  Fixpoint repeat_advance_pc (pc : addr * nat) (n : nat) : addr * nat :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.

  Local Notation call_stack := (list (addr * nat)) (only parsing).
  Local Notation loop_stack := (list (addr * nat * nat)) (only parsing).
  Inductive otbn_state : Type :=
  | otbn_busy (pc : addr * nat) (regs : regfile) (cstack : call_stack) (lstack : loop_stack)
  | otbn_error (pc : addr * nat) (errs : list string)
  | otbn_done (pc : addr * nat) (regs : regfile)
  .  
  Definition start_state (start_pc : addr * nat) : otbn_state :=
    otbn_busy start_pc map.empty [] [].
  Definition get_pc (st : otbn_state) : addr * nat :=
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
  Definition set_pc (st : otbn_state) (pc : addr * nat) (post : otbn_state -> Prop) : Prop :=
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

  (* TODO: is it possible to simplify the address logic here so we can
    directly link "dst" as a block, even if it means repeated terms? *)
  (* TODO: is it necessary to simulate some error conditions? There
     should be a difference between "OTBN had an error", which
     sometimes should in fact happen on some inputs, and "this program
     is not valid" (e.g. out-of-bounds immediate value that cannot be
     encoded). *)
  Definition ctrl1 (st : otbn_state) (i : cinsn (addr:=addr)) (post : otbn_state -> Prop) : Prop :=
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

  Fixpoint strt (regs : regfile) (insns : list sinsn) (post : regfile -> Prop) : Prop :=
    match insns with
    | [] => post regs
    | i :: insns => strt1 regs i (fun regs => strt regs insns post)
    end.

  Definition run (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs cstack lstack =>
        exists sinsns final,
        get_block pc = Some (sinsns, final)
        /\ strt regs sinsns
             (fun regs =>
                set_pc st (fst pc, (snd pc + length sinsns)%nat)
                  (fun st => set_regs st regs
                               (fun st => ctrl1 st final post)))
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
  Definition blockmap : map.map Z (block Z) := SortedListZ.map _.
  Definition objects : map.map string (list (block string)) := SortedListString.map _.
  Definition symbols : map.map string Z := SortedListString.map _.
  Import ErrorMonadNotations.

  (* Functions are conceptually just "labelled chunks of instructions
     that should always be linked sequentially." They have:
     - a name
     - a list of instructions *)
  Definition function : Type := string * list (insn (addr:=string)).

  Definition flatten_program (program : list function)
    : list (insn (addr:=string)) :=
    fold_left (fun insns fn => insns ++ snd fn) program [].

  Fixpoint get_blocks'
    (insns : list (insn (addr:=string)))
    (blocks : list (block string)) (curr : list sinsn)
    : maybe (list (block string)) :=
    match insns with
    | [] =>
        (* we should always end on a control-flow instruction *)                           
        match curr with
        | [] => Ok blocks
        | _ => Err ("Dangling straightline instructions: "
                      ++ String.concat "; " (List.map sinsn_to_string curr))
        end
    | i :: insns =>
        match i with
        | Straightline i => get_blocks' insns blocks (curr ++ [i])
        | Control i => get_blocks' insns (blocks ++ [(curr, i)]) []
        end
    end.
  Definition get_blocks (insns : list (insn (addr:=string))) : maybe (list (block string)) :=
    get_blocks' insns [] [].

  Definition get_objects (program : list function)
    : maybe (map.rep (map:=objects)) :=
    fold_left
      (fun objs fn =>
         let name := fst fn in
         let insns := snd fn in
         objs <- objs ;
         blocks <- get_blocks insns ;
         Ok (map.put objs name blocks))
      program (Ok map.empty).

  (* Returns the PC at the end of IMEM plus the symbol table. *)
  Definition get_symbols (program : list function) 
    : Z * map.rep (map:=symbols) :=
    fold_left
      (fun (pc_syms : Z * (map.rep (map:=symbols))) fn =>
         let pc := fst pc_syms in
         let syms := snd pc_syms in
         let name := fst fn in
         let insns := snd fn in
         let syms := map.put syms name pc in
         let pc := pc + (4 * Z.of_nat (length insns)) in
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
    | Loop r => Ok (Loop r)
    | Loopi imm => Ok (Loopi imm)
    | LoopEnd => Ok LoopEnd
    end.

  Definition link_block (syms : map.rep (map:=symbols)) (b : block string) : maybe (block Z) :=
    i <- link_cinsn syms (snd b) ;
    Ok (fst b, i).

  Definition block_size {addr} (b : block addr) : nat := S (length (fst b)).

  Fixpoint link_blocks
    (syms : map.rep (map:=symbols)) (curr_blocks : list (block string))
    (all_blocks : blockmap) (pc : Z) : maybe blockmap :=
    match curr_blocks with
    | [] => Ok all_blocks
    | b :: curr_blocks =>
        (b <- link_block syms b;
         link_blocks syms curr_blocks
           (map.put all_blocks pc b)
           (pc + (4 * Z.of_nat (block_size b))))
    end.

  Definition link (objs : map.rep (map:=objects))
    (syms : map.rep (map:=symbols)) : maybe blockmap :=
    map.fold
      (fun all_blocks name curr_blocks =>
         (all_blocks <- all_blocks;
          pc <- map_err (map.get syms name) ("Symbol " ++ name ++ " not found");
          link_blocks syms curr_blocks all_blocks pc))
      (Ok map.empty)
      objs.

  Definition build (program : list function)
    : maybe blockmap :=
    let syms := snd (get_symbols program) in
    objs <- get_objects program ;
    link objs syms.
End Build.

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
        [(Add x5 x2 x3 : insn);
         (Ret : insn)]).
  Definition test_program0 : list function :=
    [ ("start",
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
        [ (Addi x4 x0 0 : insn);
          (Loop x2 : insn);
          (Jal x1 "add" : insn);
          (Addi x4 x5 0 : insn);
          (LoopEnd : insn);
          (Ret : insn)]);
      add_fn ]%string.

  Compute (get_objects test_program0).
  Compute (get_symbols test_program0).
  Compute (build test_program0).

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
      build program = inl ctx
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
