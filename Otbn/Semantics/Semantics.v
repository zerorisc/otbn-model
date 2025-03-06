Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.SortedListString.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import Otbn.ISA.ISA.
Require Import Otbn.ISA.Labels.
Require Import Otbn.Util.Maybe.
Require Import Otbn.ISA.ToString.
Require Coq.Strings.HexString.
Import ListNotations.
Import MaybeNotations.
Local Open Scope Z_scope.

(*** Core semantics for the OTBN model. ***)

(* Size of DMEM. *)
Definition DMEM_BYTES := 8192.

(* Parameters to use for instantiating semantics. This allows us to
   use the same semantics definitions for both proofs (T:=Prop) and an
   executable model of OTBN (T:=maybe otbn_state). *)
Class semantics_parameters {word32 : word.word 32} (T : Type) :=
  {
    err : string -> T;
    random : (word32 -> T) -> T;
    urandom : (word32 -> T) -> T;
    option_bind : forall A, option A -> string -> (A -> T) -> T;
  }.

Section Semantics.
  Context {word32 : word.word 32} {word256 : word.word 256}.
  (* Parameterize over the representation of jump locations. *)
  Context {label : Type} {label_params : label_parameters label}.
  (* Parameterize over the map implementation. *)
  Context {regfile : map.map reg word32}
    {wregfile : map.map wreg word256}
    {flagfile : map.map flag bool}
    {mem : map.map word32 byte}
    {fetch : label * nat -> option (insn (label:=label))}.

  (* OTBN state definition *)
  Local Notation call_stack := (list (label * nat)) (only parsing).
  Local Notation loop_stack := (list (label * nat * nat)) (only parsing).
  Inductive otbn_state : Type :=
  | otbn_busy
      (pc : label * nat)      
      (regs : regfile)
      (wregs : wregfile)
      (flags : flagfile)
      (dmem : mem)
      (cstack : call_stack)
      (lstack : loop_stack)
  | otbn_error (pc : label * nat) (errs : list string)
  | otbn_done (pc : label * nat) (dmem : mem)
  .
  
  Definition get_pc (st : otbn_state) : label * nat :=
    match st with
    | otbn_busy pc _ _ _ _ _ _ => pc
    | otbn_error pc _ => pc
    | otbn_done pc _ => pc
    end.

  Definition advance_pc (pc : label * nat) := (fst pc, S (snd pc)).

  Fixpoint repeat_advance_pc (pc : label * nat) (n : nat) : label * nat :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.
  
  Definition is_valid_addi_imm (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_bn_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 1023).
  Definition is_valid_mem_offset (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_wide_mem_offset (imm : Z) : bool :=
    (-16384 <=? imm) && (imm <=? 16352) && (imm mod 32 =? 0).
  Definition is_word_aligned width (addr : word32) : bool :=
    word.eqb (word.of_Z 0) (word.and addr (word.of_Z (width - 1))).
  Definition is_valid_shift_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 248) && (imm mod 8 =? 0).

  (* Code in this section can be used either for execution or for
     omnisemantics-style proofs depending on the parameters. *) 
  Section WithSemanticsParams.
    Context {T} {semantics_params : semantics_parameters T}.
    Local Arguments option_bind {_ _ _ _}.    

    Definition read_gpr (regs : regfile) (r : gpr) (P : word32 -> T) : T :=
      match r with
      | x0 => P (word.of_Z 0) (* x0 always reads as 0 *)
      | x1 => err "Call stack reads are not currently modelled"
      | _ => option_bind (map.get regs (gpreg r))
               ("Register " ++ gpr_to_string r ++ " read but not set.")
               P
      end.

    Definition read_wdr (wregs : wregfile) (r : wdr) (P : word256 -> T) : T :=
     option_bind (map.get wregs (wdreg r))
       ("Register " ++ wdr_to_string r ++ " read but not set.")
       P.

    Definition read_flag (flags : flagfile) (f : flag) (P : bool -> T) : T :=
      option_bind (map.get flags f)
        ("Flag " ++ flag_to_string f ++ " read but not set") P.

    Definition lookup_wdr' (i : nat) : wdr :=
      (match i with
       | 0 => w0
       | 1 => w1
       | 2 => w2
       | 3 => w3
       | 4 => w4
       | 5 => w5
       | 6 => w6
       | 7 => w7
       | 8 => w8
       | 9 => w9
       | 10 => w10
       | 11 => w11
       | 12 => w12
       | 13 => w13
       | 14 => w14
       | 15 => w15
       | 16 => w16
       | 17 => w17
       | 18 => w18
       | 19 => w19
       | 20 => w20
       | 21 => w21
       | 22 => w22
       | 23 => w23
       | 24 => w24
       | 25 => w25
       | 26 => w26
       | 27 => w27
       | 28 => w28
       | 29 => w29
       | 30 => w30
       | 31 => w31
       | _ => w0 (* unreachable *)
       end)%nat.
    Definition lookup_wdr (i : word32) : wdr :=
      let i := Z.to_nat (word.unsigned (word.and i (word.of_Z 31))) in
      lookup_wdr' i.

    Definition read_wdr_indirect
      (i : word32) (wregs : wregfile) (P : word256 -> T) : T :=
      read_wdr wregs (lookup_wdr i) P.                     

    Definition read_flag_group (group : flag_group) (flags : flagfile) (P : word32 -> T) : T :=
      read_flag flags (flagM group)
        (fun m =>
           read_flag flags (flagL group)
             (fun l =>
                read_flag flags (flagZ group)
                  (fun z =>
                     read_flag flags (flagC group)
                       (fun c =>
                          let value := Z.b2z c in
                          let value := Z.lor value (Z.shiftl (Z.b2z z) 1) in
                          let value := Z.lor value (Z.shiftl (Z.b2z l) 2) in
                          let value := Z.lor value (Z.shiftl (Z.b2z m) 3) in
                          P (word.of_Z value))))).

    Definition read_csr
      (regs : regfile)
      (flags : flagfile)
      (r : csr)
      (P : word32 -> T) : T :=
      match r with
      | CSR_FG0 => read_flag_group FG0 flags P
      | CSR_FG1 => read_flag_group FG1 flags P
      | CSR_FLAGS =>
          read_flag_group FG0 flags
            (fun fg0 =>
               read_flag_group FG1 flags
                 (fun fg1 =>
                    P (word.or fg0 (word.slu fg1 (word.of_Z 4)))))
      | CSR_RND_PREFETCH => err "RND_PREFETCH register is not readable"
      | CSR_RND => random P
      | CSR_URND => urandom P
      end.

    Definition load_byte (dmem : mem) (addr : word32) (P : byte -> T) : T :=
      if word.unsigned addr <? DMEM_BYTES
      then 
        option_bind (map.get dmem addr)
          ("Memory address " ++ HexString.of_Z (word.unsigned addr) ++ " read but not set.")
          P
      else err ("Load from out-of-bounds address: " ++ HexString.of_Z (word.unsigned addr)).

    Fixpoint load_bytes (dmem : mem) (addr : word32) (len : nat) (P : list byte -> T) : T :=
      match len with
      | 0%nat => P []
      | S len =>
          load_byte dmem addr
            (fun b =>
               load_bytes dmem (word.add addr (word.of_Z 1)) len (fun bs => P (b :: bs)))
      end.      

    Definition load_word {width} {word : word.word width}
      (dmem : mem) (addr : word32) (P : word -> T) : T :=
      if is_word_aligned (width / 8) addr
      then load_bytes dmem addr (Z.to_nat (width / 8)) (fun bs => P (word.of_Z (le_combine bs)))
      else err ("Attempt to load word from unaligned address: " ++ HexString.of_Z (word.unsigned addr)).

    Definition write_gpr (regs : regfile) (r : gpr) (v : word32) (P : regfile -> T) : T :=
      match r with
      | x0 => P regs
      | x1 => err "Direct writes to the call stack via x1 are not currently modelled."
      | _ => P (map.put regs (gpreg r) v)
      end.

    Definition write_wdr (wregs : wregfile) (r : wdr) (v : word256) (P : wregfile -> T) : T :=
      P (map.put wregs (wdreg r) v).

    Definition write_flag (flags : flagfile) (f : flag) (v : bool) (P : flagfile -> T) : T :=
      P (map.put flags f v).

    Definition write_wdr_indirect
      (i : word32) (wregs : wregfile) (v : word256) (P : wregfile -> T) : T :=
      write_wdr wregs (lookup_wdr i) v P.

    Definition extract_flag (v : word32) (f : flag) (P : bool -> T) : T :=
      match f with
      | flagC _ => P (word.eqb (word.of_Z 0) (word.and v (word.of_Z 1)))
      | flagM _ => P (word.eqb (word.of_Z 0) (word.and v (word.of_Z 2)))
      | flagL _ => P (word.eqb (word.of_Z 0) (word.and v (word.of_Z 4)))
      | flagZ _ => P (word.eqb (word.of_Z 0) (word.and v (word.of_Z 8)))
      end.

    Definition write_flag_group
      (group : bool)
      (flags : flagfile)
      (v : word32)
      (P : flagfile -> T) : T :=
      extract_flag v (flagC group)
        (fun c =>
           extract_flag v (flagM group)
             (fun m =>
                extract_flag v (flagL group)
                  (fun l =>
                     extract_flag v (flagZ group)
                       (fun z =>
                          let flags := map.put flags (flagC group) c in
                          let flags := map.put flags (flagM group) m in
                          let flags := map.put flags (flagL group) l in
                          let flags := map.put flags (flagZ group) z in
                          P flags)))).

    Definition write_csr
      (regs : regfile)
      (flags : flagfile)
      (r : csr)
      (v : word32)
      (P : flagfile -> T) : T :=
      match r with
      | CSR_FG0 => write_flag_group FG0 flags v (fun flags => P flags)
      | CSR_FG1 => write_flag_group FG1 flags v (fun flags => P flags)
      | CSR_FLAGS =>
          write_flag_group FG0 flags v
            (fun flags =>
               write_flag_group FG1 flags (word.sru v (word.of_Z 4))
                 (fun flags => P flags))
      | CSR_RND_PREFETCH => P flags (* no effect on this model *)
      | CSR_RND => P flags (* writes ignored *)
      | CSR_URND => P flags (* writes ignored *)
      end.

    Definition store_byte (dmem : mem) (addr : word32) (v : byte) (P : mem -> T) : T :=
      if word.unsigned addr <? DMEM_BYTES
      then P (map.put dmem addr v)
      else err ("Store to out-of-bounds address: " ++ HexString.of_Z (word.unsigned addr)).

    Fixpoint store_bytes (dmem : mem) (addr : word32) (bs : list byte) (P : mem -> T) : T :=
      match bs with
      | [] => P dmem
      | b :: bs =>
          store_byte dmem addr b
            (fun dmem =>
               store_bytes dmem (word.add addr (word.of_Z 1)) bs P)
      end.

    Definition store_word {width} {word : word.word width}
      (dmem : mem) (addr : word32) (v : word) (P : mem -> T) : T :=
      if is_word_aligned (width / 8) addr
      then store_bytes dmem addr (le_split (Z.to_nat (width / 8)) (word.unsigned v)) P
      else err ("Attempt to store word at unaligned address: " ++ HexString.of_Z (word.unsigned addr)).
 
    Definition addi_spec (v : word32) (imm : Z) : word32 :=
      if (0 <=? imm)
      then word.add v (word.of_Z imm)
      else word.sub v (word.of_Z imm).

    Definition apply_shift (v : word256) (shift : Z) (P : word256 -> T) :=
      if is_valid_shift_imm (Z.abs shift)
      then if shift =? 0
           then P v
           else if shift >? 0
                then P (word.slu v (word.of_Z (Z.abs shift)))
                else P (word.sru v (word.of_Z (Z.abs shift)))
      else err ("Invalid shift argument: " ++ HexString.of_Z shift).

    Definition update_mlz
      (flags : flagfile) (fg : flag_group) (v : word256) (P : flagfile -> T) :=
      write_flag flags (flagM fg) (Z.testbit (word.unsigned v) 255)
        (fun flags =>
           write_flag flags (flagL fg) (Z.testbit (word.unsigned v) 0)
             (fun flags =>
                write_flag flags (flagZ fg) (word.unsigned v =? 0)
                  (fun flags => P flags))).

    Definition carry_bit (x : Z) := 2^256 <=? x.
    Definition borrow_bit (x : Z) := x <? 0.

    Local Notation "x <- f ; e" := (f (fun x => e)) (at level 100, right associativity).

    Definition strt1
      (regs : regfile) (wregs : wregfile) (flags : flagfile) (dmem : mem)
      (i : sinsn) (post : regfile -> wregfile -> flagfile -> mem -> T) : T :=
      match i with
      | Addi d x imm =>
          if is_valid_addi_imm imm
          then
            (vx <- read_gpr regs x ;
             regs <- write_gpr regs d (addi_spec vx imm) ;
             post regs wregs flags dmem)
          else err ("Invalid immediate for ADDI: " ++ HexString.of_Z imm)
      | Add d x y =>
          (vx <- read_gpr regs x ;
           vy <- read_gpr regs y ;
           regs <- write_gpr regs d (word.add vx vy) ;
           post regs wregs flags dmem)
      | Lw d x imm =>
          if is_valid_mem_offset imm
          then
            (vx <- read_gpr regs x ;
             vm <- load_word dmem (word.add vx (word.of_Z imm)) ;
             regs <- write_gpr regs d vm ;
             post regs wregs flags dmem)
          else err ("Invalid memory offset for LW: " ++ HexString.of_Z imm) 
      | Sw x y imm =>
          if is_valid_mem_offset imm
          then
            (vx <- read_gpr regs x ;
             vy <- read_gpr regs y ;
             dmem <- store_word dmem (word.add vx (word.of_Z imm)) vy ;
             post regs wregs flags dmem)
          else err ("Invalid memory offset for SW: " ++ HexString.of_Z imm)
      | Csrrs d x =>
          (vx <- read_gpr regs x ;
           vd <- read_csr regs flags d ;
           flags <- write_csr regs flags d (word.xor vd vx) ;
           regs <- write_gpr regs x vd ;
           post regs wregs flags dmem)
      | Bn_add d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           let result :=  word.add vx vy in
           wregs <- write_wdr wregs d result ;
           flags <- write_flag flags (flagC fg) (carry_bit (word.unsigned vx + word.unsigned vy)) ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem)
      | Bn_addc d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           c <- read_flag flags (flagC fg) ;
           let result := word.add (word.add vx vy) (word.of_Z (Z.b2z c)) in
           wregs <- write_wdr wregs d result ;
           flags <- write_flag flags (flagC fg)
                      (carry_bit (word.unsigned vx + word.unsigned vy + Z.b2z c)) ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem)
      | Bn_addi d x imm fg =>
          if is_valid_bn_imm imm
          then
            (vx <- read_wdr wregs x ;
             let result := word.add vx (word.of_Z imm) in
             wregs <- write_wdr wregs d result ;
             flags <- write_flag flags (flagC fg) (carry_bit (word.unsigned vx + imm)) ;
           flags <- update_mlz flags fg result ;
             post regs wregs flags dmem)
          else err ("Invalid immediate for BN.ADDI: " ++ HexString.of_Z imm)
      | Bn_and d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           let result := word.and vx vy in
           wregs <- write_wdr wregs d result ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem)
      | Bn_xor d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           let result := word.xor vx vy in
           wregs <- write_wdr wregs d result ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem)
      | Bn_lid d dinc x xinc imm =>
          if is_valid_wide_mem_offset imm
          then
            (vx <- read_gpr regs x ;
             let addr := (word.add vx (word.of_Z imm)) in
             vm <- load_word dmem addr ;
             id <- read_gpr regs d ;
             wregs <- write_wdr_indirect id wregs vm ;
             if dinc
             then if xinc
                  then err ("Both increment bits set for BN.LID.")
                  else
                    (regs <- write_gpr regs d (word.add id (word.of_Z 1)) ;
                     post regs wregs flags dmem)
             else if xinc
                  then
                    (regs <- write_gpr regs x (word.add vx (word.of_Z 32)) ;
                     post regs wregs flags dmem)
                  else post regs wregs flags dmem)
          else err ("Invalid memory offset for BN.LID: " ++ HexString.of_Z imm)
      | Bn_sid x xinc y yinc imm =>
          if is_valid_wide_mem_offset imm
          then
            (ix <- read_gpr regs x ;
             vx <- read_wdr_indirect ix wregs ;
             vy <- read_gpr regs y ;
             let addr := (word.add vy (word.of_Z imm)) in
             dmem <- store_word dmem addr vx ;
             if xinc
             then if yinc
                  then err ("Both increment bits set for BN.SID.")
                  else
                    (regs <- write_gpr regs x (word.add ix (word.of_Z 1)) ;
                     post regs wregs flags dmem)
             else if yinc
                  then 
                    (regs <- write_gpr regs y (word.add vy (word.of_Z 32)) ;
                     post regs wregs flags dmem)
                  else post regs wregs flags dmem)
          else err ("Invalid memory offset for BN.SID: " ++ HexString.of_Z imm)
      end.

    (* Pop an address off the call stack and jump to that location. *)
    Definition call_stack_pop (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          option_bind
            (hd_error cstack)
            "Attempt to read from empty call stack!"
            (fun dst => post (otbn_busy dst regs wregs flags dmem (tl cstack) lstack))
      | _ => post st
      end.

    (* Push the next (one-advanced) PC onto the call stack. *)
    Definition call_stack_push (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          if (length cstack <? 8)%nat
          then post (otbn_busy pc regs wregs flags dmem ((advance_pc pc) :: cstack) lstack)
          else err "Attempt to write to a full call stack!"
      | _ => post st
      end.
    Definition program_exit (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack => post (otbn_done pc dmem)
      | _ => post st
      end.
    Definition set_pc
      (st : otbn_state) (pc : label * nat) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy _ regs wregs flags dmem cstack lstack =>
          post (otbn_busy pc regs wregs flags dmem cstack lstack)
      | _ => post st
      end.
    Definition update_state
      (st : otbn_state)
      (regs : regfile)
      (wregs : wregfile)
      (flags : flagfile)
      (dmem : mem)
      (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc _ _ _ _ cstack lstack =>
          post (otbn_busy pc regs wregs flags dmem cstack lstack)
      | _ => post st
      end.
    Definition next_pc (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          post (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)
      | _ => post st
      end.
    Definition read_gpr_from_state (st : otbn_state) (r : gpr) (post : _ -> T) : T :=
      match st with
      | otbn_busy _ regs _ _ _ _ _ => read_gpr regs r post
      | _ => err "GPR values cannot be read from non-busy OTBN states."
      end.

    (* Begin a new loop. *)
    Definition loop_start
      (st : otbn_state) (iters : nat) (post : otbn_state -> T) : T :=
      match iters with
      | O => err "Number of loop iterations cannot be 0."
      | S iters =>
          match st with
          | otbn_busy pc regs wregs flags dmem cstack lstack =>          
              let start_pc := advance_pc pc in
              if (length lstack <? 8)%nat
              then post (otbn_busy
                           start_pc regs wregs flags dmem cstack
                           ((start_pc, iters) :: lstack))
              else err "Loop stack full!"
          | _ => err "Cannot start a loop in a non-busy OTBN state."
          end
      end.

    (* Finish a loop iteration (and potentially the entire loop).
       Expects that the current PC matches the loop-body end PC of the
       first loop stack entry. *)
    Definition loop_end (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          option_bind (hd_error lstack)
                      "Cannot end loop if loop stack is empty."
                      (fun start_iters =>
                             match (snd start_iters) with
                             | O => post (otbn_busy
                                            (advance_pc pc) regs wregs flags dmem cstack
                                            (tl lstack))
                             | S iters =>
                                 post (otbn_busy
                                         (fst start_iters) regs wregs flags dmem cstack
                                         ((fst start_iters, iters) :: tl lstack))
                             end)
      | _ => err "Cannot end a loop in a non-busy OTBN state."
      end.

  (* TODO: is it necessary to simulate some error conditions? There
     should be a difference between "OTBN had an error", which
     sometimes should in fact happen on some inputs, and "this program
     is not valid" (e.g. out-of-bounds immediate value that cannot be
     encoded). *)
  Definition ctrl1
    (st : otbn_state) (i : cinsn (label:=label))
    (post : otbn_state -> T) : T :=
    match i with
    | Ret =>  call_stack_pop st post
    | Ecall => program_exit st post
    | Jal r dst =>
        match r with
        | x0 => set_pc st (dst, 0%nat) post
        | x1 => call_stack_push st (fun st => set_pc st (dst, 0%nat) post)
        | _ => err "JAL with registers other than x1 is currently not modelled."
        end
    | Bne r1 r2 dst =>
        read_gpr_from_state st r1
          (fun v1 =>
             read_gpr_from_state st r2
               (fun v2 =>
                  if (word.eqb v1 v2)
                  then next_pc st post
                  else set_pc st (dst, 0%nat) post))
    | Beq r1 r2 dst =>
        read_gpr_from_state st r1
          (fun v1 =>
             read_gpr_from_state st r2
               (fun v2 =>
                  if (word.eqb v1 v2)
                  then set_pc st (dst, 0%nat) post
                  else next_pc st post))
    | Loopi v => loop_start st v post
    | Loop r => read_gpr_from_state st r
                  (fun v => loop_start st (Z.to_nat (word.unsigned v)) post)
    | LoopEnd => loop_end st post
    end.
  End WithSemanticsParams.
  
  Global Instance proof_semantics {word32 : word.word 32} : semantics_parameters Prop :=
    {|
      err := fun _ => False;
      random := fun P => forall v, P v;
      urandom := fun P => forall v, P v;
      option_bind := fun _ x _ f => exists v, x = Some v /\ f v;
    |}.

  (* TODO: randomness is currently modelled as an error, but we could
     eventually present a list of random numbers or something. *)  
  Global Instance exec_semantics : semantics_parameters (maybe otbn_state) :=
    {|
      err := fun msg => Err msg;
      random := fun _ => Err "Randomness not currently supported in executable model";
      urandom := fun _ => Err "Randomness not currently supported in executable model";
      option_bind := fun _ x msg f => match x with
                                      | Some x => f x
                                      | None => Err msg
                                      end;
    |}%maybe.

  (* Prop model for proofs *)
  Definition run1 (st : otbn_state) (post : otbn_state -> Prop) : Prop :=
    match st with
    | otbn_busy pc regs wregs flags dmem cstack lstack =>
        exists i,
        fetch pc = Some i
        /\ match i with
           | Straightline i =>
               strt1 regs wregs flags dmem i
                 (fun regs wregs flags dmem =>
                    update_state st regs wregs flags dmem
                      (fun st => set_pc st (advance_pc pc) post))
           | Control i => ctrl1 st i post
           end
    | _ => post st
    end.
  
  (* Fully executable model. *)
  Definition exec1 (st : otbn_state) : maybe otbn_state :=
    match st with
    | otbn_busy pc regs wregs flags dmem cstack lstack =>
        option_bind
          _
          (fetch pc)
          ("No instruction found at PC " ++ pc_to_string pc)%string
          (fun i =>
             prefix_err
               (match i with
                | Straightline i =>
                    (strt1 regs wregs flags dmem i
                       (fun regs wregs flags dmem =>
                          update_state st regs wregs flags dmem
                            (fun st => set_pc st (advance_pc pc) Ok)))
                | Control i => ctrl1 st i Ok
                end)
               ("PC " ++ pc_to_string pc ++ " (" ++ insn_to_string i ++ "): "))
    | _ => Ok st
    end.

  Definition is_busy (st : otbn_state) : bool :=
    match st with
    | otbn_busy _ _ _ _ _ _ _ => true
    | _ => false
    end.
  Fixpoint exec (st : otbn_state) (fuel : nat) : maybe otbn_state :=
    match fuel with
    | O => Err "Simulation ran out of fuel."
    | S fuel =>
        (st <- exec1 st;
         if is_busy st
         then exec st fuel
         else Ok st)
    end%maybe.
End Semantics.

Module Coercions.
  Coercion Straightline : sinsn >-> insn.
  Coercion Control : cinsn >-> insn.
End Coercions.

(* Functions consist of a name, internal labels (map of string ->
   offset within the function), and a list of instructions. *)
Definition symbols : map.map string nat := SortedListString.map _.
Instance symbols_ok : map.ok symbols := (SortedListString.ok nat).
Definition otbn_function : Type := string * symbols * list (insn (label:=string)).

(* Convenience shorthands for defining function specs. *)
Section Specs.
  Context {word32 : word.word 32} {word256 : word.word 256}.
  Context {label : Type} {label_params : label_parameters label}.
  Context {regfile : map.map reg word32}
    {wregfile : map.map wreg word256}
    {flagfile : map.map flag bool}
    {mem : map.map word32 byte}
    {fetch : label * nat -> option (insn (label:=label))}.

  (* Spec builder for a function that returns to its caller. *)
  Definition returns
    {label : Type} {fetch:label * nat -> option insn}
    (start : label) regs wregs flags dmem cstack lstack
    (spec : regfile -> wregfile -> flagfile -> mem -> Prop) : Prop :=
    forall ret_pc,
      hd_error cstack = Some ret_pc ->
      eventually
        (run1 (fetch:=fetch))
        (fun st =>
           match st with
           | otbn_busy pc regs' wregs' flags' dmem' cstack' lstack' =>
               pc = ret_pc
               /\ spec regs' wregs' flags' dmem'
               /\ cstack' = tl cstack
               /\ lstack' = lstack
           | _ => False
           end)
        (otbn_busy (start, 0%nat) regs wregs flags dmem cstack lstack).

  (* Spec builder for a function that exits the program. *)
  Definition exits
    {label : Type} {fetch: label * nat -> option insn}
    (start : label) regs wregs flags dmem cstack lstack
    (spec : mem -> Prop) (err_spec : _ -> Prop)
    : Prop :=
    eventually
      (run1 (fetch:=fetch))
      (fun st =>
         match st with
         | otbn_done pc dmem => spec dmem
         | otbn_error pc errs => err_spec errs
         | _ => False
         end)
      (otbn_busy (start, 0%nat) regs wregs flags dmem cstack lstack).

  (* Convenience start state builder (for fully linked programs). *)
  Definition start_state (dmem : mem) : otbn_state :=
    otbn_busy (0%nat, 0%nat) map.empty map.empty map.empty dmem [] [].
End Specs.

(* Separation-logic definitions. *)
Notation bytes_at ptr bs := (eq (map.of_list_word_at ptr bs)) (only parsing).
Definition word_at {word32 : word.word 32} {mem : map.map word32 byte}
  {width} {word : word.word width}
  (ptr : word32) (v : word) : mem -> Prop :=
  bytes_at ptr (le_split (Z.to_nat (width / 8)) (word.unsigned v)).
Notation word32_at := (word_at (width:=32)) (only parsing).
Notation word256_at := (word_at (width:=256)) (only parsing).

(* Get the offset of a (string) label within a function. *)
Definition get_label_offset
  (fn : otbn_function) (label : string) : option nat :=
  let fn_name := fst (fst fn) in
  let fn_syms := snd (fst fn) in
  if (String.eqb label fn_name)
  then Some 0%nat
  else map.get fn_syms label.

(* Fetch an instruction from a function. *)
Definition fetch_fn
  (fn : otbn_function) (pc : string * nat) : option insn :=
  let label := fst pc in
  let offset := snd pc in
  let fn_insns := snd fn in
  match get_label_offset fn label with
  | None => None
  | Some label_offset => nth_error fn_insns (label_offset + offset)
  end. 

(* Fetch an instruction from a collection of functions. *)
Definition fetch_ctx
  (fns : list otbn_function) (pc : string * nat) : option insn :=
  fold_left
    (fun res fn =>
       match res, fetch_fn fn pc with
       | None, Some i => Some i
       | _,_ => res
       end)
    fns None.

(* Programs are lists of instructions that link to each other with
   offsets within the global program. This represents code
   post-linking. *)
Definition program : Type := list (insn (label:=nat)).

(* Fetch from a whole program. *)
Definition fetch
  (prog : program) (pc : nat * nat) : option insn :=
  let global_offset := fst pc in
  let fn_offset := snd pc in
  nth_error prog (global_offset + fn_offset).
