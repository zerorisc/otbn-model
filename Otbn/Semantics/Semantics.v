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
Class semantics_parameters (T : Type) :=
  {
    err : string -> T;
    random : forall {width} {word : word.word width}, (word -> T) -> T;
    urandom : forall {width} {word : word.word width}, (word -> T) -> T;
    option_bind : forall A, option A -> string -> (A -> T) -> T;
  }.

(* Types of OTBN software errors. *)
Inductive otbn_software_error :=
| BAD_DATA_ADDR
| BAD_INSN_ADDR
| CALL_STACK
| ILLEGAL_INSN
| KEY_INVALID
| LOOP
.

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
  | otbn_error (pc : label * nat) (err : otbn_software_error)
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
  
  Definition is_valid_lui_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 1048575).
  Definition is_valid_shamt (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 31).
  Definition is_valid_arith32_imm (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_arith256_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 1023).
  Definition is_valid_rshi_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 255).
  Definition is_valid_mem_offset (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_wide_mem_offset (imm : Z) : bool :=
    (-16384 <=? imm) && (imm <=? 16352) && (imm mod 32 =? 0).
  Definition is_valid_wdr_index (i : Z) : bool :=
    (0 <=? i) && (i <=? 31).
  Definition is_word_aligned width (addr : word32) : bool :=
    word.eqb (word.of_Z 0) (word.and addr (word.of_Z (width - 1))).
  Definition is_valid_arith256_shift_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 248) && (imm mod 8 =? 0).
  Definition is_valid_mulqacc_shift (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 192) && (imm mod 64 =? 0).

  (* Code in this section can be used either for execution or for
     omnisemantics-style proofs depending on the parameters. *) 
  Section WithSemanticsParams.
    Context {T} {semantics_params : semantics_parameters T}.
    Local Arguments option_bind {_ _ _}.

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
    
    Definition read_wsr (wregs : wregfile) (r : wsr) (P : word256 -> T) : T :=
      match r with
      | WSR_RND => random P
      | WSR_URND => urandom P
      | _ => 
          option_bind (map.get wregs (wsreg r))
            ("Register " ++ wsr_to_string r ++ " read but not set.")
            P
      end.

    Definition read_limb (wregs : wregfile) (l : limb) (P : word256 -> T) : T :=
      match l with
      | (r, 0) =>
          read_wdr wregs r
            (fun v => P (word.and v (word.of_Z (Z.ones 64))))
      | (r, 1) =>
          read_wdr wregs r
            (fun v => P (word.and (word.sru v (word.of_Z 64)) (word.of_Z (Z.ones 64))))
      | (r, 2) =>
          read_wdr wregs r
            (fun v => P (word.and (word.sru v (word.of_Z 128)) (word.of_Z (Z.ones 64))))
      | (r, 3) =>
          read_wdr wregs r
            (fun v => P (word.and (word.sru v (word.of_Z 192)) (word.of_Z (Z.ones 64))))
      | (r, n) => err ("Invalid BN.MULQACC quarter-word selector for "
                         ++ wdr_to_string r ++ ": "
                         ++ (if (n <? 0) then "-" else "") ++ String.of_nat (Z.to_nat (Z.abs n)))
      end.
 
    Definition lookup_wdr (i : Z) : wdr :=
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
       end).

    Definition read_wdr_indirect
      (i : word32) (wregs : wregfile) (P : word256 -> T) : T :=
      read_wdr wregs (lookup_wdr (word.unsigned i)) P.                     

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

    (* Completely errors out if the read data was not initialized. In
       reality, this would *probably* return a DMEM_INTG_ERROR
       (because memory is randomized along with its integrity bits)
       but because it's not certain it should never be used as a
       program's expected behavior, even on invalid inputs. *)
    Fixpoint load_bytes (dmem : mem) (addr : word32) (len : nat) (P : list byte -> T) : T :=      
      match len with
      | 0%nat => P []
      | S len => option_bind
                   (map.get dmem addr)
                   ("Attempt to read from uninitialized DMEM at address: "
                      ++ HexString.of_Z (word.unsigned addr))
                   (fun b => load_bytes dmem (word.add addr (word.of_Z 1)) len
                               (fun bs => P (b :: bs)))
      end.

    (* Use this to trigger *OTBN* error conditions. This is subtly
       distinct from the `err` with a debug message in Semantics, because
       it can be used for errors that are expected under certain
       conditions and part of a program's spec. *)
    Definition assert_or_error
      (err_bits : option otbn_software_error) (cond : bool) (err_code : otbn_software_error)
      (P : option otbn_software_error -> T) : T :=
      if cond then P err_bits else P (Some err_code).

    Definition load_word {width} {word : word.word width}
      (dmem : mem) (addr : word32) (P : word -> T) : T :=
      load_bytes dmem addr (Z.to_nat (width / 8)) (fun bs => P (word.of_Z (le_combine bs))).

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

    Definition write_wsr
      (wregs : wregfile) (r : wsr) (v : word256) (P : wregfile -> T) : T :=
      match r with
      | WSR_MOD => P (map.put wregs (wsreg r) v)
      | WSR_ACC => P (map.put wregs (wsreg r) v)
      | WSR_RND => P wregs (* writes ignored *)
      | WSR_URND => P wregs (* writes ignored *)
      | WSR_KEY_S0_L => P wregs (* writes ignored *)
      | WSR_KEY_S0_H => P wregs (* writes ignored *)
      | WSR_KEY_S1_L => P wregs (* writes ignored *)
      | WSR_KEY_S1_H => P wregs (* writes ignored *)
      end.
  
    Definition write_wdr_indirect
      (i : word32) (wregs : wregfile) (v : word256) (P : wregfile -> T) : T :=
      write_wdr wregs (lookup_wdr (word.unsigned i)) v P.

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

    Fixpoint store_bytes (dmem : mem) (addr : word32) (bs : list byte) (P : mem -> T) : T :=
      match bs with
      | [] => P dmem
      | b :: bs => store_bytes (map.put dmem addr b) (word.add addr (word.of_Z 1)) bs P
      end.

    Definition store_word {width} {word : word.word width}
      (dmem : mem) (addr : word32) (v : word) (P : mem -> T) : T :=
      store_bytes dmem addr (le_split (Z.to_nat (width / 8)) (word.unsigned v)) P.
 
    Definition addi_spec (v : word32) (imm : Z) : word32 :=
      if (0 <=? imm)
      then word.add v (word.of_Z imm)
      else word.sub v (word.of_Z (Z.abs imm)).

    Definition apply_shift (v : word256) (shift : Z) (P : word256 -> T) :=
      if is_valid_arith256_shift_imm (Z.abs shift)
      then if shift =? 0
           then P v
           else if shift >? 0
                then P (word.slu v (word.of_Z (Z.abs shift)))
                else P (word.sru v (word.of_Z (Z.abs shift)))
      else err ("Invalid shift argument: " ++ HexString.of_Z shift).

    Definition update_mlz
      (flags : flagfile) (fg : flag_group) (v : word256) (P : flagfile -> T) : T:=
      write_flag flags (flagM fg) (Z.testbit (word.unsigned v) 255)
        (fun flags =>
           write_flag flags (flagL fg) (Z.testbit (word.unsigned v) 0)
             (fun flags =>
                write_flag flags (flagZ fg) (word.unsigned v =? 0)
                  (fun flags => P flags))).

    Definition read_gpr_inc (regs : regfile) (x : gpr_inc) (P : word32 -> T) : T :=
      match x with
      | gpr_inc_true r => read_gpr regs r P
      | gpr_inc_false r => read_gpr regs r P
      end.

    Definition increment_gprs
      (regs : regfile) (x y : gpr_inc) (xinc : Z) (yinc : Z)
      (P : regfile -> option otbn_software_error -> T) : T :=
      match x, y with
      | gpr_inc_true rx, gpr_inc_true ry => P regs (Some ILLEGAL_INSN)              
      | gpr_inc_true rx, gpr_inc_false ry =>
          read_gpr regs rx
            (fun vx =>
               write_gpr regs rx (word.add vx (word.of_Z xinc))
                 (fun regs => P regs None))
      | gpr_inc_false rx, gpr_inc_true ry =>
          read_gpr regs ry
            (fun vy =>
               write_gpr regs ry (word.add vy (word.of_Z yinc))
                 (fun regs => P regs None))
      | gpr_inc_false rx, gpr_inc_false ry => P regs None
      end.
 
    Definition carry_bit (x : Z) := 2^256 <=? x.
    Definition borrow_bit (x : Z) := x <? 0.

    Definition rshi_spec (x y : word256) (s : Z) : word256 :=
      word.of_Z (Z.shiftr (word.unsigned x + Z.shiftl (word.unsigned y) 256) s).
    Definition addm_spec (x y m : word256) : word256 :=
      if (word.unsigned m <? word.unsigned x + word.unsigned y)
      then word.of_Z (word.unsigned x + word.unsigned y - word.unsigned m)
      else word.add x y.
    Definition subm_spec (x y m : word256) : word256 :=
      if (word.unsigned y <? word.unsigned x)
      then word.of_Z (word.unsigned x + word.unsigned m - word.unsigned y)
      else word.sub x y.
    Definition mulqacc_spec (acc x y : word256) (s : Z) : word256 :=
      word.add acc (word.of_Z (Z.shiftl (word.unsigned x * word.unsigned y) s)).
    (* helper for mulqacc half-word writebacks *)
    Definition so_writeback_spec (u : bool) (vd result : word256) : word256 :=
      if u
      then word.or (word.slu result (word.of_Z 128)) (word.and vd (word.of_Z (Z.ones 128)))
      else word.or (word.and result (word.of_Z (Z.ones 128)))
             (word.and vd (word.slu (word.of_Z (Z.ones 128)) (word.of_Z 128))).

    Local Notation "x <- f ; e" := (f (fun x => e)) (at level 100, right associativity).

    (* convenience for instructions that are basic word ops *)
    Definition word32_binop (op : word32 -> word32 -> word32) (regs : regfile) (d x y : gpr)
      (post : regfile -> T) : T :=
      (vx <- read_gpr regs x ;
       vy <- read_gpr regs y ;
       regs <- write_gpr regs d (op vx vy) ;
       post regs).
    Definition word32_unop (op : word32 -> word32) (regs : regfile) (d x : gpr)
      (post : regfile -> T) : T :=
      (vx <- read_gpr regs x ;
       regs <- write_gpr regs d (op vx) ;
       post regs).
    Definition word256_binop
      (op : word256 -> word256 -> word256) (wregs : wregfile) (flags : flagfile)
      (d x y : wdr) (s : Z) (fg : flag_group) (post : wregfile -> flagfile -> T) : T :=
      (vx <- read_wdr wregs x ;
       vy <- read_wdr wregs y ;
       vy <- apply_shift vy s ;
       let result := op vx vy in
       wregs <- write_wdr wregs d result ;
       flags <- update_mlz flags fg result ;
       post wregs flags).

    Definition strt1
      (regs : regfile) (wregs : wregfile) (flags : flagfile) (dmem : mem)
      (i : sinsn)
      (post : regfile -> wregfile -> flagfile -> mem -> option otbn_software_error -> T) : T :=
      let err_bits : option otbn_software_error := None in
      match i with
      | Addi d x imm =>
          if is_valid_arith32_imm imm
          then
            (vx <- read_gpr regs x ;
             regs <- write_gpr regs d (addi_spec vx imm) ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for ADDI: " ++ HexString.of_Z imm)
      | Lui d imm =>
          if is_valid_lui_imm imm
          then
            (regs <- write_gpr regs d (word.of_Z (Z.shiftl imm 12)) ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for LUI: " ++ HexString.of_Z imm)
      | Add d x y => word32_binop word.add regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Sub d x y => word32_binop word.sub regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Sll d x y => word32_binop word.slu regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Slli d x imm =>
          if is_valid_shamt imm
          then word32_unop (fun x => word.slu x (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for SLLI: " ++ HexString.of_Z imm)
      | Srl d x y => word32_binop word.sru regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Srli d x imm =>
          if is_valid_shamt imm
          then word32_unop (fun x => word.sru x (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for SRLI: " ++ HexString.of_Z imm)
      | Sra d x y => word32_binop word.srs regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Srai d x imm =>
          if is_valid_shamt imm
          then word32_unop (fun x => word.slu x (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for SRAI: " ++ HexString.of_Z imm)
      | And d x y => word32_binop word.and regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Andi d x imm =>
          if is_valid_arith32_imm imm
          then word32_unop (word.and (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for ANDI: " ++ HexString.of_Z imm)
      | Xor d x y => word32_binop word.xor regs d x y
                       (fun regs => post regs wregs flags dmem err_bits)
      | Xori d x imm =>
          if is_valid_arith32_imm imm
          then word32_unop (word.xor (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for XORI: " ++ HexString.of_Z imm)
      | Or d x y => word32_binop word.or regs d x y
                      (fun regs => post regs wregs flags dmem err_bits)
      | Ori d x imm =>
          if is_valid_arith32_imm imm
          then word32_unop (word.or (word.of_Z imm))
                 regs d x (fun regs => post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for ORI: " ++ HexString.of_Z imm)
      | Lw d x imm =>
          if is_valid_mem_offset imm
          then
            (vx <- read_gpr regs x ;
             let addr := word.add vx (word.of_Z imm) in
             err_bits <- assert_or_error err_bits (is_word_aligned 4 addr) BAD_DATA_ADDR ;
             err_bits <- assert_or_error
                           err_bits (word.unsigned addr + 4 <? DMEM_BYTES) BAD_DATA_ADDR ;
             vm <- load_word dmem addr ;
             regs <- write_gpr regs d vm ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid memory offset for LW: " ++ HexString.of_Z imm) 
      | Sw x y imm =>
          if is_valid_mem_offset imm
          then
            (vx <- read_gpr regs x ;
             vy <- read_gpr regs y ;
             let addr := word.add vy (word.of_Z imm) in
             err_bits <- assert_or_error err_bits (is_word_aligned 4 addr) BAD_DATA_ADDR ;
             err_bits <- assert_or_error
                           err_bits (word.unsigned addr + 4 <? DMEM_BYTES) BAD_DATA_ADDR ;
             dmem <- store_word dmem addr vx ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid memory offset for SW: " ++ HexString.of_Z imm)
      | Csrrs d x y =>
          (vx <- read_csr regs flags x ;
           vy <- read_gpr regs y ;
           flags <- write_csr regs flags x (word.or vx vy) ;
           regs <- write_gpr regs d vx ;
           post regs wregs flags dmem err_bits)
      | Csrrw d x y =>
          (vx <- read_csr regs flags x ;
           vy <- read_gpr regs y ;
           flags <- write_csr regs flags x vy ;
           regs <- write_gpr regs d vx ;
           post regs wregs flags dmem err_bits)
      | Bn_and d x y s fg => word256_binop word.and wregs flags d x y s fg
                               (fun wregs flags => post regs wregs flags dmem err_bits)
      | Bn_xor d x y s fg => word256_binop word.xor wregs flags d x y s fg
                               (fun wregs flags => post regs wregs flags dmem err_bits)
      | Bn_or d x y s fg => word256_binop word.or wregs flags d x y s fg
                              (fun wregs flags => post regs wregs flags dmem err_bits)
      | Bn_not d x s fg =>
          (vx <- read_wdr wregs x ;
           vx <- apply_shift vx s ;
           let result := word.not vx in
           wregs <- write_wdr wregs d result ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem err_bits)
      | Bn_rshi d x y s =>
          if is_valid_rshi_imm s
          then
            (vx <- read_wdr wregs x ;
             vy <- read_wdr wregs y ;
             wregs <- write_wdr wregs d (rshi_spec vx vy s) ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for BN.RSHI: " ++ HexString.of_Z s)  
      | Bn_sel d x y f =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vf <- read_flag flags f ;
           wregs <- write_wdr wregs d (if vf then vx else vy) ;
           post regs wregs flags dmem err_bits)
      | Bn_cmp x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           flags <- write_flag flags (flagC fg)
                      (borrow_bit (word.unsigned vx - word.unsigned vy)) ;
           flags <- update_mlz flags fg (word.sub vx vy) ;
           post regs wregs flags dmem err_bits)
      | Bn_cmpb x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           c <- read_flag flags (flagC fg) ;
           flags <- write_flag flags (flagC fg)
                      (borrow_bit (word.unsigned vx - word.unsigned vy - Z.b2z c)) ;
           flags <- update_mlz flags fg (word.sub (word.sub vx vy) (word.of_Z (Z.b2z c))) ;
           post regs wregs flags dmem err_bits)
      | Bn_add d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           let result :=  word.add vx vy in
           wregs <- write_wdr wregs d result ;
           flags <- write_flag flags (flagC fg) (carry_bit (word.unsigned vx + word.unsigned vy)) ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem err_bits)
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
           post regs wregs flags dmem err_bits)
      | Bn_addi d x imm fg =>
          if is_valid_arith256_imm imm
          then
            (vx <- read_wdr wregs x ;
             let result := word.add vx (word.of_Z imm) in
             wregs <- write_wdr wregs d result ;
             flags <- write_flag flags (flagC fg) (carry_bit (word.unsigned vx + imm)) ;
             flags <- update_mlz flags fg result ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for BN.ADDI: " ++ HexString.of_Z imm)
      | Bn_sub d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           let result :=  word.sub vx vy in
           wregs <- write_wdr wregs d result ;
           flags <- write_flag flags (flagC fg)
                      (borrow_bit (word.unsigned vx - word.unsigned vy)) ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem err_bits)
      | Bn_subb d x y s fg =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vy <- apply_shift vy s ;
           c <- read_flag flags (flagC fg) ;
           let result := word.sub (word.sub vx vy) (word.of_Z (Z.b2z c)) in
           wregs <- write_wdr wregs d result ;
           flags <- write_flag flags (flagC fg)
                      (borrow_bit (word.unsigned vx - word.unsigned vy - Z.b2z c)) ;
           flags <- update_mlz flags fg result ;
           post regs wregs flags dmem err_bits)
      | Bn_subi d x imm fg =>
          if is_valid_arith256_imm imm
          then
            (vx <- read_wdr wregs x ;
             let result := word.sub vx (word.of_Z imm) in
             wregs <- write_wdr wregs d result ;
             flags <- write_flag flags (flagC fg) (borrow_bit (word.unsigned vx - imm)) ;
             flags <- update_mlz flags fg result ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid immediate for BN.SUBI: " ++ HexString.of_Z imm)
      | Bn_addm d x y =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vm <- read_wsr wregs WSR_MOD;           
           wregs <- write_wdr wregs d (addm_spec vx vy vm) ;
           post regs wregs flags dmem err_bits)
      | Bn_subm d x y =>
          (vx <- read_wdr wregs x ;
           vy <- read_wdr wregs y ;
           vm <- read_wsr wregs WSR_MOD;           
           wregs <- write_wdr wregs d (subm_spec vx vy vm) ;
           post regs wregs flags dmem err_bits)
      | Bn_mulqacc z x y s =>
          if is_valid_mulqacc_shift s
          then
            (vx <- read_limb wregs x ;
             vy <- read_limb wregs y ;
             acc <- if z then read_wsr wregs WSR_ACC else (fun P => P (word.of_Z 0)) ;
             wregs <- write_wsr wregs WSR_ACC (mulqacc_spec acc vx vy s) ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid shift for BN.MULQACC: " ++ HexString.of_Z s)
      | Bn_mulqacc_wo z d x y s fg =>
          if is_valid_mulqacc_shift s
          then
            (vx <- read_limb wregs x ;
             vy <- read_limb wregs y ;
             acc <- if z then read_wsr wregs WSR_ACC else (fun P => P (word.of_Z 0)) ;
             let result := mulqacc_spec acc vx vy s in
             wregs <- write_wsr wregs WSR_ACC result ;
             wregs <- write_wdr wregs d result ;
             flags <- update_mlz flags fg result ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid shift for BN.MULQACC.WO: " ++ HexString.of_Z s)
      | Bn_mulqacc_so z d u x y s fg =>
          if is_valid_mulqacc_shift s
          then
            (vx <- read_limb wregs x ;
             vy <- read_limb wregs y ;
             vd <- read_wdr wregs d ;
             acc <- if z then read_wsr wregs WSR_ACC else (fun P => P (word.of_Z 0)) ;
             let result := mulqacc_spec acc vx vy s in
             wregs <- write_wsr wregs WSR_ACC (word.sru result (word.of_Z 128)) ;
             let wb := so_writeback_spec u vd result in
             wregs <- write_wdr wregs d wb ;
             flags <- write_flag flags (flagZ fg) (word.unsigned wb =? 0) ;
             flags <- if u
                      then write_flag flags (flagM fg) (Z.testbit (word.unsigned wb) 255)
                      else write_flag flags (flagL fg) (Z.testbit (word.unsigned wb) 0) ;
             post regs wregs flags dmem err_bits)
          else err ("Invalid shift for BN.MULQACC.SO: " ++ HexString.of_Z s)
      | Bn_lid dinc xinc imm =>
          if is_valid_wide_mem_offset imm
          then
            (vx <- read_gpr_inc regs xinc ;
             let addr := word.add vx (word.of_Z imm) in
             err_bits <- assert_or_error err_bits (is_word_aligned 32 addr) BAD_DATA_ADDR ;
             err_bits <- assert_or_error
                           err_bits (word.unsigned addr + 32 <? DMEM_BYTES) BAD_DATA_ADDR ;
             vm <- load_word dmem addr ;
             id <- read_gpr_inc regs dinc ;
             err_bits <- assert_or_error
                           err_bits (is_valid_wdr_index (word.unsigned id)) ILLEGAL_INSN ;
             wregs <- write_wdr_indirect id wregs vm ;
             increment_gprs regs dinc xinc 1 32
               (fun regs err_bits =>
                  post regs wregs flags dmem err_bits))
          else err ("Invalid memory offset for BN.LID: " ++ HexString.of_Z imm)
      | Bn_sid xinc yinc imm =>
          if is_valid_wide_mem_offset imm
          then
            (ix <- read_gpr_inc regs xinc ;
             err_bits <- assert_or_error
                           err_bits (is_valid_wdr_index (word.unsigned ix)) ILLEGAL_INSN ;
             vx <- read_wdr_indirect ix wregs ;
             vy <- read_gpr_inc regs yinc ;
             let addr := word.add vy (word.of_Z imm) in
             err_bits <- assert_or_error err_bits (is_word_aligned 32 addr) BAD_DATA_ADDR ;
             err_bits <- assert_or_error
                           err_bits (word.unsigned addr + 32 <? DMEM_BYTES) BAD_DATA_ADDR ;
             dmem <- store_word dmem addr vx ;
             increment_gprs regs xinc yinc 1 32
               (fun regs err_bits =>
                  post regs wregs flags dmem err_bits))
          else err ("Invalid memory offset for BN.SID: " ++ HexString.of_Z imm)
      | Bn_mov d x =>
          (vx <- read_wdr wregs x ;
           wregs <- write_wdr wregs d vx ;
           post regs wregs flags dmem err_bits)
      | Bn_movr dinc xinc =>
          (ix <- read_gpr_inc regs xinc ;
           err_bits <- assert_or_error
                         err_bits (is_valid_wdr_index (word.unsigned ix)) ILLEGAL_INSN ;
           vx <- read_wdr_indirect ix wregs ;
           id <- read_gpr_inc regs dinc ;
           err_bits <- assert_or_error
                         err_bits (is_valid_wdr_index (word.unsigned id)) ILLEGAL_INSN ;
           wregs <- write_wdr_indirect id wregs vx ;
           increment_gprs regs dinc xinc 1 1
             (fun regs err_bits =>
                post regs wregs flags dmem err_bits))
      | Bn_wsrr d x =>
          (vx <- read_wsr wregs x ;
           wregs <- write_wdr wregs d vx ;
           post regs wregs flags dmem err_bits)
      | Bn_wsrw d x =>
          (vx <- read_wdr wregs x ;
           wregs <- write_wsr wregs d vx ;
           post regs wregs flags dmem err_bits)
      end.

    (* Pop an address off the call stack and jump to that location. *)
    Definition call_stack_pop (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          match cstack with
          | dst :: cstack => 
              post (otbn_busy dst regs wregs flags dmem cstack lstack)
          | [] => post (otbn_error pc CALL_STACK)
          end
      | _ => post st
      end.

    (* Push the next (one-advanced) PC onto the call stack. *)
    Definition call_stack_push (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          if (length cstack <? 8)%nat
          then post (otbn_busy pc regs wregs flags dmem ((advance_pc pc) :: cstack) lstack)
          else post (otbn_error pc CALL_STACK)
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
      (err_bits : option otbn_software_error)
      (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc _ _ _ _ cstack lstack =>
          match err_bits with
          | Some err_bits => post (otbn_error pc err_bits)
          | None => post (otbn_busy pc regs wregs flags dmem cstack lstack)
          end
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
      | O => post (otbn_error (get_pc st) LOOP) (* loop cannot have 0 iterations *)
      | S iters =>
          match st with
          | otbn_busy pc regs wregs flags dmem cstack lstack =>          
              let start_pc := advance_pc pc in
              if (length lstack <? 8)%nat
              then post (otbn_busy
                           start_pc regs wregs flags dmem cstack
                           ((start_pc, iters) :: lstack))
              else post (otbn_error pc LOOP)
          | _ => err "Cannot start a loop in a non-busy OTBN state."
          end
      end.

    (* Finish a loop iteration (and potentially the entire loop).
       Expects that the current PC matches the loop-body end PC of the
       first loop stack entry. *)
    Definition loop_end (st : otbn_state) (post : otbn_state -> T) : T :=
      match st with
      | otbn_busy pc regs wregs flags dmem cstack lstack =>
          match lstack with
          | (start, iters) :: lstack =>
              match iters with
              | O => post (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)
              | S iters =>
                  post (otbn_busy start regs wregs flags dmem cstack ((start, iters) :: lstack))
              end
          | [] => post (otbn_error pc LOOP)
          end
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
    | Unimp => post (otbn_error (get_pc st) ILLEGAL_INSN)
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

  Global Instance proof_semantics : semantics_parameters Prop :=
    {|
      err := fun _ => False;
      random := fun width word (P : _ -> Prop) => forall v, P v;
      urandom := fun width word (P : _ -> Prop) => forall v, P v;
      option_bind := fun _ x _ f => exists v, x = Some v /\ f v;
    |}.

  (* TODO: randomness is currently modelled as an error, but we could
     eventually present a list of random numbers or something. *)  
  Global Instance exec_semantics : semantics_parameters (maybe otbn_state) :=
    {|
      err := fun msg => Err msg;
      random := fun _ _ _ => Err "Randomness not currently supported in executable model";
      urandom := fun _ _ _ => Err "Randomness not currently supported in executable model";
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
                 (fun regs wregs flags dmem err_bits =>
                    update_state st regs wregs flags dmem err_bits
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
                       (fun regs wregs flags dmem err_bits =>
                          update_state st regs wregs flags dmem err_bits
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

(* Experimental way to smoothly insert symbols without manual calculations. *)
Fixpoint make_symbols
  (body : list (string * insn (label:=string))) (offset : nat) : symbols :=
  match body with
  | (EmptyString, _) :: body => make_symbols body (S offset)
  | (s, _) :: body => map.put (make_symbols body (S offset)) s offset
  | [] => map.empty
  end.
Fixpoint make_insns (body : list (string * insn (label:=string))) : list insn :=
  match body with
  | (_, i) :: body => i :: make_insns body
  | [] => []
  end.
Definition make_function name body : otbn_function :=  
  (name, make_symbols body 0, make_insns body).

Ltac make_function name body :=
  let val := eval cbv [make_function make_insns make_symbols] in (make_function name body) in
    exact val.
