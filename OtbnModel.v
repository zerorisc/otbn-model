Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Coq.Strings.HexString.
Import ListNotations.
Local Open Scope Z_scope.

(*** Model of OTBN. ***)

(* Size of DMEM. *)
Definition DMEM_BYTES := 8192.

Section Registers.
  (* General data registers, 32 bits each. *)
  (* x0 is always wired to 0, x1 is the call stack. *)
  Inductive gpr : Type :=
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31.

  (* Wide data registers, 256 bits each. *)
  Inductive wdr : Type :=
  | w0  | w1  | w2  | w3  | w4  | w5  | w6  | w7  | w8  | w9  | w10 | w11 | w12 | w13 | w14 | w15
  | w16 | w17 | w18 | w19 | w20 | w21 | w22 | w23 | w24 | w25 | w26 | w27 | w28 | w29 | w30 | w31.

  (* Control and status registers, 32 bits each. *)
  Inductive csr : Type :=
  | CSR_FG0
  | CSR_FG1
  | CSR_FLAGS
      (* Omit these registers for now, they are ~never used in practice.
  | CSR_MOD0
  | CSR_MOD1
  | CSR_MOD2
  | CSR_MOD3
  | CSR_MOD4
  | CSR_MOD5
  | CSR_MOD6
  | CSR_MOD7
       *)
  | CSR_RND_PREFETCH
  | CSR_RND
  | CSR_URND
  .

  (* Wide status registers, 256 bits each. *)
  Inductive wsr : Type :=
  | WSR_MOD
  | WSR_RND
  | WSR_URND
  | WSR_ACC
  | WSR_KEY_S0_L
  | WSR_KEY_S0_H
  | WSR_KEY_S1_L
  | WSR_KEY_S1_H
  .

  (* Catchall type indicating any 32-bit register. *)
  Inductive reg :=
  | gpreg : gpr -> reg
  | csreg : csr -> reg
  .

  (* Catchall type indicating any 256-bit register. *)
  Inductive wreg :=
  | wdreg : wdr -> wreg
  | wsreg : wsr -> wreg
  .

  Inductive flag :=
  | flagM : bool -> flag
  | flagL : bool -> flag
  | flagZ : bool -> flag
  | flagC : bool -> flag.
End Registers.

Section ISA.
  (* Straightline instructions (no control flow) *)
  Inductive sinsn : Type :=
  | Addi : gpr -> gpr -> Z -> sinsn
  | Add : gpr -> gpr -> gpr -> sinsn
  | Lw : gpr -> gpr -> Z -> sinsn
  | Sw : gpr -> gpr -> Z -> sinsn
  | Csrrs : csr -> gpr -> sinsn
  .

  (* Control-flow instructions *)
  Inductive cinsn {label : Type} : Type :=
  (* TODO: technically ret is a special case of JALR, but only RET is used in practice *)
  | Ret : cinsn
  | Ecall : cinsn
  | Jal : gpr -> label -> cinsn
  | Bne : gpr -> gpr -> label -> cinsn
  | Beq : gpr -> gpr -> label -> cinsn
  (* Note: loops here use an end instruction instead of an iteration
     count to make codegen and processing easier. *)
  | Loop : gpr -> cinsn
  | Loopi : nat -> cinsn
  | LoopEnd : cinsn
  .

  Inductive insn {label : Type} : Type :=
  | Straightline : sinsn -> insn
  | Control : cinsn (label:=label) -> insn
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

(* Representation of jump locations (e.g. string, numerical offset). *)
Class label_parameters {label : Type} :=
  {
    label_eqb : label -> label -> bool;
    label_to_string : label -> string;
    pc_to_string : label * nat -> string;
  }.
Global Arguments label_parameters : clear implicits.

Class label_parameters_ok {label} (params: label_parameters label) :=
  {
    label_eqb_spec : forall d1 d2, BoolSpec (d1 = d2) (d1 <> d2) (label_eqb d1 d2)
  }.

Instance string_label_parameters : label_parameters string :=
  {|
    label_eqb := String.eqb;
    label_to_string := id;
    pc_to_string := fun pc => (fst pc ++ "+" ++ HexString.of_Z (4 * Z.of_nat (snd pc)))%string;
  |}.

Instance nat_label_parameters : label_parameters nat :=
  {|
    label_eqb := Nat.eqb;
    label_to_string := HexString.of_nat;
    pc_to_string := fun pc => HexString.of_Z (4 * Z.of_nat (fst pc + snd pc));
  |}.

Section Stringify.
  Context {word32 : word.word 32}.
  Context {label : Type} {label_params : label_parameters label}.

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
    | x8 => "x8"
    | x9 => "x9"
    | x10 => "x10"
    | x11 => "x11"
    | x12 => "x12"
    | x13 => "x13"
    | x14 => "x14"
    | x15 => "x15"
    | x16 => "x16"
    | x17 => "x17"
    | x18 => "x18"
    | x19 => "x19"
    | x20 => "x20"
    | x21 => "x21"
    | x22 => "x22"
    | x23 => "x23"
    | x24 => "x24"
    | x25 => "x25"
    | x26 => "x26"
    | x27 => "x27"
    | x28 => "x28"
    | x29 => "x29"
    | x30 => "x30"
    | x31 => "x31"
    end.
  Local Coercion gpr_to_string : gpr >-> string.

  Definition csr_to_string (r : csr) : string :=
    match r with
    | CSR_FG0 => "CSR_FG0"
    | CSR_FG1 => "CSR_FG1"
    | CSR_FLAGS => "CSR_FLAGS"
    | CSR_RND_PREFETCH => "CSR_RND_PREFETCH"
    | CSR_RND => "CSR_RND"
    | CSR_URND => "CSR_URND"
    end.
  Local Coercion csr_to_string : csr >-> string.

  Definition reg_to_string (r : reg) : string :=
    match r with
    | gpreg r => r
    | csreg r => r
    end.

  Definition wdr_to_string (r : wdr) : string :=
    match r with
    | w0 => "w0"
    | w1 => "w1"
    | w2 => "w2"
    | w3 => "w3"
    | w4 => "w4"
    | w5 => "w5"
    | w6 => "w6"
    | w7 => "w7"
    | w8 => "w8"
    | w9 => "w9"
    | w10 => "w10"
    | w11 => "w11"
    | w12 => "w12"
    | w13 => "w13"
    | w14 => "w14"
    | w15 => "w15"
    | w16 => "w16"
    | w17 => "w17"
    | w18 => "w18"
    | w19 => "w19"
    | w20 => "w20"
    | w21 => "w21"
    | w22 => "w22"
    | w23 => "w23"
    | w24 => "w24"
    | w25 => "w25"
    | w26 => "w26"
    | w27 => "w27"
    | w28 => "w28"
    | w29 => "w29"
    | w30 => "w30"
    | w31 => "w31"
    end.
  Local Coercion wdr_to_string : wdr >-> string.

  Definition wsr_to_string (r : wsr) : string :=
    match r with
    | WSR_MOD => "WSR_MOD"
    | WSR_RND => "WSR_RND"
    | WSR_URND => "WSR_URND"
    | WSR_ACC => "WSR_ACC"
    | WSR_KEY_S0_L => "WSR_KEY_S0_L"
    | WSR_KEY_S0_H => "WSR_KEY_S0_H"
    | WSR_KEY_S1_L => "WSR_KEY_S1_L"
    | WSR_KEY_S1_H => "WSR_KEY_S1_H"
    end.
  Local Coercion wsr_to_string : wsr >-> string.

  Definition wreg_to_string (r : wreg) : string :=
    match r with
    | wdreg r => r
    | wsreg r => r
    end.

  Definition flag_to_string (f : flag) : string :=
    match f with
    | flagM false => "FG0.M"
    | flagM true  => "FG1.M"
    | flagL false => "FG0.L"
    | flagL true  => "FG1.L"
    | flagZ false => "FG0.Z"
    | flagZ true  => "FG1.Z"
    | flagC false => "FG0.C"
    | flagC true  => "FG1.C"
    end.

  Definition sinsn_to_string (i : sinsn) : string :=
    match i with
    | Addi rd rs imm =>
        "addi " ++ rd ++ ", " ++ rs ++ ", " ++ HexString.of_Z imm
    | Add rd rs1 rs2 =>
        "add " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Lw rd rs imm =>
        "lw" ++ rd ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs
    | Sw rs1 rs2 imm =>
        "sw" ++ rs2 ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs1
    | Csrrs rd rs =>
        "csrrs " ++ rd ++ ", " ++ rs ++ ", "
    end.

  Definition cinsn_to_string (i : cinsn (label:=label)) : string :=
    match i with
    | Ret => "ret"
    | Ecall => "ecall"
    | Jal r dst => "jal " ++ r ++ ", " ++ label_to_string dst
    | Bne r1 r2 dst => "bne " ++ r1 ++ ", " ++ r2 ++ ", " ++ label_to_string dst
    | Beq r1 r2 dst => "beq " ++ r1 ++ ", " ++ r2 ++ ", " ++ label_to_string dst
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
Import ErrorMonadNotations.

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

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
    {mem : map.map word32 word32}
    {fetch : label * nat -> option (insn (label:=label))}.

  Definition advance_pc (pc : label * nat) := (fst pc, S (snd pc)).

  Definition is_valid_addi_imm (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_mem_offset (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_addr (addr : word32) : bool :=
    word.eqb (word.of_Z 0) (word.and addr (word.of_Z 3))
    && (word.unsigned addr + 4 <? DMEM_BYTES).

  Fixpoint repeat_advance_pc (pc : label * nat) (n : nat) : label * nat :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.

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

  (* Code in this section can be used either for execution or for
     omnisemantics-style proofs depending on the parameters. *) 
  Section ExecOrProof.
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

    Definition read_flag_group (group : bool) (flags : flagfile) (P : word32 -> T) : T :=
      option_bind
        (map.get flags (flagM group))
        ("Flag M in group " ++ if group then "1" else "0" ++ " read but not set.")
        (fun m =>
           option_bind
             (map.get flags (flagL group))
             ("Flag L in group " ++ if group then "1" else "0" ++ " read but not set.")
             (fun l =>
                option_bind
                  (map.get flags (flagZ group))
                  ("Flag Z in group " ++ if group then "1" else "0" ++ " read but not set.")
                  (fun z =>
                     option_bind
                       (map.get flags (flagC group))
                       ("Flag C in group " ++ if group then "1" else "0" ++ " read but not set.")
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
      | CSR_FG0 => read_flag_group false flags P
      | CSR_FG1 => read_flag_group true flags P
      | CSR_FLAGS =>
          read_flag_group false flags
            (fun fg0 =>
               read_flag_group true flags
                 (fun fg1 =>
                    P (word.or fg0 (word.slu fg1 (word.of_Z 4)))))
      | CSR_RND_PREFETCH => err "RND_PREFETCH register is not readable"
      | CSR_RND => random P
      | CSR_URND => urandom P
      end.

    Definition read_mem (dmem : mem) (addr : word32) (P : word32 -> T) : T :=
      if is_valid_addr addr
      then option_bind (map.get dmem addr)
             ("Memory address " ++ HexString.of_Z (word.unsigned addr) ++ " read but not set.")
             P
      else err ("Memory read from invalid address: " ++ HexString.of_Z (word.unsigned addr)).

    Definition write_gpr (regs : regfile) (r : gpr) (v : word32) (P : regfile -> T) : T :=
      match r with
      | x0 => P regs
      | x1 => err "Direct writes to the call stack via x1 are not currently modelled."
      | _ => P (map.put regs (gpreg r) v)
      end.

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
      (P : regfile -> flagfile -> T) : T :=
      match r with
      | CSR_FG0 => write_flag_group false flags v (fun flags => P regs flags)
      | CSR_FG1 => write_flag_group true flags v (fun flags => P regs flags)
      | CSR_FLAGS =>
          write_flag_group false flags v
            (fun flags =>
               write_flag_group true flags (word.sru v (word.of_Z 4))
                 (fun flags => P regs flags))
      | CSR_RND_PREFETCH => P regs flags (* no effect on this model *)
      | CSR_RND => P regs flags (* writes ignored *)
      | CSR_URND => P regs flags (* writes ignored *)
      end.

    Definition write_mem (dmem : mem) (addr v : word32) (P : mem -> T) : T :=
      if is_valid_addr addr
      then P (map.put dmem addr v)
      else err ("Memory write to invalid address: " ++ HexString.of_Z (word.unsigned addr)).

    Definition addi_spec (v : word32) (imm : Z) : word32 :=
      if (0 <=? imm)
      then word.add v (word.of_Z imm)
      else word.sub v (word.of_Z imm).

    Definition bignum_combine (v0 v1 v2 v3 v4 v5 v6 v7: word32) : word256 :=
      let v := word.unsigned v0 in
      let v := Z.lor v (Z.shiftl (word.unsigned v1) 32) in
      let v := Z.lor v (Z.shiftl (word.unsigned v2) 64) in
      let v := Z.lor v (Z.shiftl (word.unsigned v3) 96) in
      let v := Z.lor v (Z.shiftl (word.unsigned v4) 128) in
      let v := Z.lor v (Z.shiftl (word.unsigned v5) 160) in
      let v := Z.lor v (Z.shiftl (word.unsigned v6) 192) in
      let v := Z.lor v (Z.shiftl (word.unsigned v7) 224) in
      word.of_Z v.

    Definition bignum_store (dmem : mem) (addr : word32) (v : word256) (P : mem -> T) : T :=
      let v := word.unsigned v in
      write_mem dmem addr (word.of_Z v)
        (fun dmem =>
           write_mem dmem (word.add addr (word.of_Z 4)) (word.of_Z (Z.shiftr v 32))
             (fun dmem =>
                write_mem dmem (word.add addr (word.of_Z 8)) (word.of_Z (Z.shiftr v 64))
                  (fun dmem =>
                     write_mem dmem (word.add addr (word.of_Z 12)) (word.of_Z (Z.shiftr v 96))
                       (fun dmem =>
                          write_mem dmem
                            (word.add addr (word.of_Z 16)) (word.of_Z (Z.shiftr v 128))
                            (fun dmem =>
                               write_mem dmem
                                 (word.add addr (word.of_Z 20)) (word.of_Z (Z.shiftr v 160))
                                 (fun dmem =>
                                    write_mem dmem
                                      (word.add addr (word.of_Z 24)) (word.of_Z (Z.shiftr v 192))
                                      (fun dmem =>
                                         write_mem dmem
                                           (word.add addr (word.of_Z 28))
                                           (word.of_Z (Z.shiftr v 224)) P))))))).

    Definition bignum_load (dmem : mem) (addr : word32) (P : word256 -> T) : T :=
      read_mem dmem addr
        (fun v0 =>
           read_mem dmem (word.add addr (word.of_Z 4))
             (fun v1 =>
                read_mem dmem (word.add addr (word.of_Z 8))
                  (fun v2 =>
                     read_mem dmem (word.add addr (word.of_Z 12))
                       (fun v3 =>
                          read_mem dmem (word.add addr (word.of_Z 16))
                            (fun v4 =>
                               read_mem dmem (word.add addr (word.of_Z 20))
                                 (fun v5 =>
                                    read_mem dmem (word.add addr (word.of_Z 24))
                                      (fun v6 =>
                                         read_mem dmem (word.add addr (word.of_Z 28))
                                           (fun v7 =>
                                              P (bignum_combine v0 v1 v2 v3 v4 v5 v6 v7))))))))).
 
    Definition strt1
      (regs : regfile) (wregs : wregfile) (flags : flagfile) (dmem : mem)
      (i : sinsn) (post : regfile -> wregfile -> flagfile -> mem -> T) : T :=
      match i with
      | Addi d x imm =>
          if is_valid_addi_imm imm
          then
            read_gpr regs x
              (fun vx =>
                 write_gpr regs d (addi_spec vx imm)
                   (fun regs => post regs wregs flags dmem))
          else err ("Invalid immediate for ADDI: " ++ HexString.of_Z imm)
      | Add d x y =>
          read_gpr regs x
            (fun vx =>
               read_gpr regs y
                 (fun vy =>
                    write_gpr regs d (word.add vx vy)
                      (fun regs => post regs wregs flags dmem)))
      | Lw d x imm =>
          if is_valid_mem_offset imm
          then read_gpr regs x
                 (fun vx =>
                    read_mem dmem (word.add vx (word.of_Z imm))
                      (fun vm =>
                         write_gpr regs d vm
                           (fun regs => post regs wregs flags dmem)))
          else err ("Invalid memory offset for LW: " ++ HexString.of_Z imm) 
      | Sw x y imm =>
          if is_valid_mem_offset imm
          then read_gpr regs x
                 (fun vx =>
                    (read_gpr regs y
                       (fun vy =>
                          write_mem dmem (word.add vx (word.of_Z imm)) vy
                            (fun dmem => post regs wregs flags dmem))))
          else err ("Invalid memory offset for SW: " ++ HexString.of_Z imm)
      | Csrrs d x =>
          read_gpr regs x
            (fun vx =>
               read_csr regs flags d
                 (fun vd =>
                    write_csr regs flags d (word.xor vd vx)
                      (fun regs flags =>
                         write_gpr regs x vd
                           (fun regs => post regs wregs flags dmem))))
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
  End ExecOrProof.
  
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
    |}.

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
    end.
End Semantics.

Require Import coqutil.Map.SortedListZ.
Require Import coqutil.Map.SortedListString.
Local Coercion Straightline : sinsn >-> insn.
Local Coercion Control : cinsn >-> insn.

(* Contains a way to link programs. *)
Section Build.           
  Definition symbols : map.map string nat := SortedListString.map _.
  (* Functions consist of a name, internal labels (map of string ->
     offset within the function), and a list of instructions. *)
  Definition function : Type := string * symbols * list (insn (label:=string)).
  (* Programs are lists of instructions that link to each other with
     offsets within the global program. This represents code
     post-linking. *)
  Definition program : Type := list (insn (label:=nat)).

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
    (syms : map.rep (map:=symbols)) (i : cinsn (label:=string))
    : maybe (cinsn (label:=nat)) :=
    match i with
    | Ret => Ok Ret
    | Ecall => Ok Ecall
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
    | LoopEnd => Ok LoopEnd
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
    (i1 : cinsn (label:=string))
    (i2 : cinsn (label:=nat)) : Prop :=
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
  Context {word32 : word.word 32} {regfile : map.map reg word32}.
  Context {word256 : word.word 256} {wregfile : map.map wreg word256}.
  Context {flagfile : map.map flag bool} {mem : map.map word32 word32}.

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

  Lemma add_symbol_fail start_syms label label_offset1 label_offset2 :
    map.get start_syms label = Some label_offset1 ->
    exists msg,
      add_symbol start_syms label label_offset2 = Err msg.
  Proof.
    cbv [add_symbol]; intros. destruct_one_match; try congruence.
    eauto.
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

  Lemma link_symbols_for_function_name_fail :
    forall fn start_syms start_offset name label_offset,
      name = fst (fst fn) ->
      map.get start_syms name = Some label_offset ->
      exists msg,
        link_symbols_for_function (start_syms, start_offset) fn = Err msg.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function]; cbn [bind fst snd]; intros.
    subst. lazymatch goal with H : map.get _ _ = Some _ |- _ =>
                                 eapply add_symbol_fail in H; destruct H end.
    rewrite H. err_simpl. eauto.
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

  Lemma link_symbols'_name_fail fn name :
    forall fns start_syms start_offset label_offset,
      In fn fns ->
      name = fst (fst fn) ->
      map.get start_syms name = Some label_offset ->
      exists msg,
        link_symbols' start_syms start_offset fns = Err msg.
  Proof.
    cbv [program_size link_symbols']; induction fns; cbn [In]; intros;
      repeat lazymatch goal with
        | H : False |- _ => contradiction H
        | H : _ \/ _ |- _ => destruct H
        | H : map.get _ _ = Some _ |- context [link_symbols_for_function _ fn] =>
            eapply link_symbols_for_function_name_fail in H; [ | reflexivity .. ];
            destruct H as [? H]; rewrite H; err_simpl; solve [eauto]
        | _ => progress (cbn [maybe_fold_left]; subst)
        end; [ ].
    err_simpl; eauto.
    destruct_products; cbn [fst snd] in *.
    eauto using link_symbols_for_function_no_overwrite.
  Qed.

  Lemma add_symbol_correct start_syms label label_offset syms :
      add_symbol start_syms label label_offset = Ok syms ->
      map.get syms label = Some label_offset.
  Proof.
    cbv [add_symbol]; destruct_one_match; intros; err_simpl; auto using map.get_put_same.
  Qed.

  Lemma merge_symbols_correct fn_syms global_offset global_syms :
    forall syms,
      merge_symbols global_offset global_syms fn_syms = Ok syms ->
      (forall label label_offset,
          map.get fn_syms label = Some label_offset ->
          map.get syms label = Some (global_offset + label_offset)%nat).
  Proof.
    cbv [merge_symbols].
    apply map.fold_spec.
    { intros. rewrite map.get_empty in *. congruence. }
    { intros. err_simpl.
      repeat lazymatch goal with
             | H : map.get (map.put _ ?x _) ?y = Some _ |- _ =>
                 destr (String.eqb x y);
                 [ rewrite map.get_put_same in H
                 | rewrite map.get_put_diff in H by congruence ]
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             end;
        eauto using add_symbol_correct, add_symbol_no_overwrite. }
  Qed.

  Lemma get_label_offset_name fn name :
    name = fst (fst fn) ->
    get_label_offset fn name = Some 0%nat.
  Proof.
    intros; subst. cbv [get_label_offset].
    destruct_one_match; congruence.
  Qed.

  Lemma link_symbols_for_function_correct
    fn start_syms start_offset syms end_offset dst fn_offset :
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      get_label_offset fn dst = Some fn_offset ->
      map.get syms dst = Some (start_offset + fn_offset)%nat.
  Proof.
    destruct fn as [[fn_name fn_syms] fn_insns].
    cbv [link_symbols_for_function get_label_offset].
    cbn [bind fst snd]; intros; err_simpl.
    destruct_one_match_hyp; [ | solve [eauto using merge_symbols_correct] ].
    lazymatch goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end.
    rewrite Nat.add_0_r.
    eauto using add_symbol_correct, merge_symbols_no_overwrite.
  Qed.

  Lemma link_symbols_for_function_name fn start_syms start_offset syms end_offset :
      link_symbols_for_function (start_syms, start_offset) fn = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some start_offset.
  Proof.
    intros. replace start_offset with (start_offset + 0)%nat by lia.
    eapply link_symbols_for_function_correct; eauto; [ ].
    apply get_label_offset_name; reflexivity.
  Qed.

  Lemma link_symbols'_correct :
    forall fns1 fns2 fn start_syms start_offset syms end_offset fn_offset dst,
    link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = inl (syms, end_offset) ->
    get_label_offset fn dst = Some fn_offset ->
    map.get syms dst = Some (program_size start_offset fns1 + fn_offset)%nat.
  Proof.
    cbv [program_size]; induction fns1; intros.
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

  Lemma link_symbols'_name :
    forall fns1 fns2 fn start_syms start_offset syms end_offset,
      link_symbols' start_syms start_offset (fns1 ++ fn :: fns2) = Ok (syms, end_offset) ->
      map.get syms (fst (fst fn)) = Some (program_size start_offset fns1).
  Proof.
    intros.
    replace (program_size start_offset fns1)
      with (program_size start_offset fns1 + 0)%nat by lia.
    eapply link_symbols'_correct; eauto using get_label_offset_name.
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

  Definition pcs_related (syms : symbols) (pc1 : string * nat) (pc2 : nat * nat) : Prop :=
    map.get syms (fst pc1) = Some (fst pc2) /\ snd pc1 = snd pc2.
  Definition loop_stack_entries_related (syms : symbols) (e1 : _ * nat) (e2 : _ * nat) : Prop :=
    pcs_related syms (fst e1) (fst e2) /\ snd e1 = snd e2.
  Definition states_related (syms : symbols)
    (st1 : otbn_state (label:=string)) (st2 : otbn_state (label:=nat)) : Prop :=
    match st1, st2 with
    | otbn_busy pc1 regs1 wregs1 flags1 dmem1 cstack1 lstack1,
      otbn_busy pc2 regs2 wregs2 flags2 dmem2 cstack2 lstack2 =>
        pcs_related syms pc1 pc2
        /\ regs1 = regs2
        /\ wregs1 = wregs2
        /\ flags1 = flags2
        /\ dmem1 = dmem2
        /\ Forall2 (pcs_related syms) cstack1 cstack2
        /\ Forall2 (loop_stack_entries_related syms) lstack1 lstack2
    | otbn_done pc1 dmem1, otbn_done pc2 dmem2 =>
        pcs_related syms pc1 pc2
        /\ dmem1 = dmem2
    | otbn_error pc1 errs1, otbn_error pc2 errs2 =>
        pcs_related syms pc1 pc2
        /\ errs1 = errs2
    | _, _ => False
    end.

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

  Lemma fetch_fn_Some fn pc i :
      fetch_fn fn pc = Some i ->
      exists offset,
        get_label_offset fn (fst pc) = Some offset
        /\ nth_error (snd fn) (offset + snd pc) = Some i.
  Proof.
    cbv [fetch_fn]. destruct_one_match; [ | congruence ].
    intros. eexists; ssplit; [ reflexivity .. | ].
    assumption.
  Qed.

  Lemma fetch_ctx_Some :
    forall fns pc i,
      fetch_ctx fns pc = Some i ->    
      exists fn,
        fetch_fn fn pc = Some i
        /\ In fn fns.
  Proof.
    cbv [fetch_ctx].
    induction fns as [|fn fns]; cbn [fold_left]; [ congruence | ].
    intros. destruct_one_match_hyp.
    { rewrite fetch_ctx_done in *.
      lazymatch goal with H : Some _ = Some _ |- _ => inversion H; clear H; subst end.
      eexists; ssplit; eauto using in_eq. }
    { repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | H : fold_left _ _ None = Some _ |- _ => apply IHfns in H
             end.
      eexists; ssplit; eauto using in_cons. }
  Qed.

  Lemma link_symbols_correct fns fn syms fn_offset dst n :
    link_symbols fns = inl syms ->
    nth_error fns n = Some fn ->
    get_label_offset fn dst = Some fn_offset ->
    map.get syms dst = Some (program_size 0 (firstn n fns) + fn_offset)%nat.
  Proof.
    cbv [link_symbols]. intros. err_simpl. destruct_products.
    Search nth_error app.
    repeat lazymatch goal with
           | H : nth_error _ _ = Some _ |- _ =>
               apply nth_error_split in H
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           end.
    subst. rewrite List.firstn_app_l by reflexivity. cbn [fst snd].
    eauto using link_symbols'_correct.
  Qed.

  Lemma link_fetch syms prog fns pc1 pc2 i1 :
    link fns = Ok prog ->
    link_symbols fns = Ok syms ->
    pcs_related syms pc1 pc2 ->
    fetch_ctx fns pc1 = Some i1 ->
    exists i2,
      fetch prog pc2 = Some i2
      /\ insn_equiv syms i1 i2.
  Proof.
    cbv [pcs_related]; intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : fetch_ctx _ _ = Some _ |- _ => apply fetch_ctx_Some in H
           end.
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H; subst
           | H : exists _, _ |- _ => destruct H
           | H : fetch_fn ?fn (fst (fst ?fn), _) = Some _ |- _ => rewrite fetch_fn_name in H
    
           | H : fetch_fn _ _ = Some _ |- _ => apply fetch_fn_Some in H
           | H : @nth_error insn _ ?n = Some _, H' : linked_at _ _ _ _ |- _ =>
               specialize (H' n ltac:(eauto using List.nth_error_Some_bound_index))
           end.

    lazymatch goal with
    | H : nth_error ?l ?i = Some ?x, H' : nth_error ?l ?i = Some ?y |- _ =>
        assert (x = y) by congruence; subst
    end.
 
    pose proof (link_symbols_correct
                  _ _ _ _ _ _
                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    lazymatch goal with
    | H : map.get ?m ?k = Some ?x, H' : map.get ?m ?k = Some ?y |- _ =>
        assert (x = y) by congruence; subst
    end.

    lazymatch goal with
    | H : fetch prog _ = Some ?i |- _ => exists i
    end.
    ssplit; [ | assumption .. ].
    destruct_products.
    cbv [fetch] in *. cbn [fst snd] in *. subst.
    lazymatch goal with
    | H : _ = Some ?x |- _ = Some ?x => rewrite <-H
    end.
    repeat (f_equal; try lia).
  Qed.

  Lemma read_gpr_weaken regs r P Q :
    read_gpr regs r P ->
    (forall regs, P regs -> Q regs) ->
    read_gpr regs r Q.
  Proof.
    cbv [read_gpr err option_bind proof_semantics]; intros; destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma read_csr_weaken regs flags r P Q :
    read_csr regs flags r P ->
    (forall regs, P regs -> Q regs) ->
    read_csr regs flags r Q.
  Proof.
    cbv [read_csr read_flag_group err random urandom option_bind proof_semantics]; intros.
    destruct r;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma read_mem_weaken dmem addr P Q :
    read_mem dmem addr P ->
    (forall dmem, P dmem -> Q dmem) ->
    read_mem dmem addr Q.
  Proof.
    cbv [read_mem err option_bind proof_semantics]; intros.
    destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma write_gpr_weaken regs r v P Q :
    write_gpr regs r v P ->
    (forall regs, P regs -> Q regs) ->
    write_gpr regs r v Q.
  Proof.
    cbv [write_gpr err proof_semantics]; intros; destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma write_csr_weaken regs flags r v P Q :
    write_csr (T:=Prop) regs flags r v P ->
    (forall regs flags, P regs flags -> Q regs flags) ->
    write_csr (T:=Prop) regs flags r v Q.
  Proof.
    cbv [write_csr write_flag_group extract_flag]; intros; destruct_one_match; eauto.
  Qed.

  Lemma write_mem_weaken dmem addr v P Q :
    write_mem dmem addr v P ->
    (forall dmem, P dmem -> Q dmem) ->
    write_mem dmem addr v Q.
  Proof.
    cbv [write_mem]; intros; destruct_one_match; eauto.
  Qed.

  Lemma strt1_weaken regs wregs flags dmem i P Q :
    strt1 regs wregs flags dmem i P ->
    (forall regs wregs flags dmem, P regs wregs flags dmem -> Q regs wregs flags dmem) ->
    strt1 regs wregs flags dmem i Q.
  Proof.
    cbv [strt1 err proof_semantics]; intros; repeat destruct_one_match;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- read_gpr _ _ _ =>
            eapply read_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_mem _ _ _ =>
            eapply read_mem_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ =>
            eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_csr _ _ _ _ _ =>
            eapply write_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_mem _ _ _ _ =>
            eapply write_mem_weaken; [ eassumption | ]; cbv beta; intros
        | |- Q _ _ _ _ => solve [eauto]
        end.
  Qed.

  Ltac related_states_hammer :=
    cbn [states_related] in *;
      repeat lazymatch goal with
        | H : False |- _ => contradiction H
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H; subst
        | H : forall st1' st2', _ st1' st2' -> _ st1' -> ?spec2 st2' |- ?spec2 _ =>
            eapply H; [ | eassumption ]
        | H : Forall2 _ (_ :: _) _ |- _ =>
            inversion H; clear H; subst; cbn [hd_error tl] in *
        | H : context [match ?x with _ => _ end] |- _ => destruct_one_match_hyp
        | |- context [match ?x with _ => _ end] => destruct_one_match
        | H : hd_error ?l = Some _ |- _ =>
            destruct l; cbn [hd_error tl] in *                                               
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | H : None = Some _ |- _ => exfalso; congruence
        | |- pcs_related _ _ _ =>
            progress cbv [advance_pc pcs_related] in *; cbn [fst snd]; ssplit; eauto
        | |- loop_stack_entries_related _ _ _ =>
            progress cbv [loop_stack_entries_related] in *; ssplit
        | |- states_related _ _ _ =>
            progress cbv [states_related]; try contradiction; ssplit; eauto
        | H: Forall2 _ ?l1 ?l2,
            H0 : (length ?l1 < ?n)%nat, H1 : (?n <= length ?l2)%nat |- _ =>
            pose proof (Forall2_length H); lia
        | |- Forall2 _ (_ :: _) (_ :: _) => constructor
        | |- read_gpr _ _ _ =>
            eapply read_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_mem _ _ _ =>
            eapply read_mem_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ =>
            eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_csr _ _ _ _ _ =>
            eapply write_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_mem _ _ _ _ =>
            eapply write_mem_weaken; [ eassumption | ]; cbv beta; intros
        | |- exists _, _ =>
            eexists; ssplit; first [ eassumption
                                   | reflexivity
                                   | solve [related_states_hammer] ]
        | _ => first [ progress (cbv [call_stack_pop call_stack_push
                                        loop_start loop_end loop_stack_entries_related
                                        read_gpr_from_state next_pc
                                        set_pc update_state program_exit] in *;
                                 cbn [fst snd err option_bind proof_semantics] in *; subst )
                     | congruence
                     | solve [eauto] ]
        end.

  Lemma ctrl1_weaken syms i1 i2 st1 st2 spec1 spec2 :
    ctrl1 (label:=string) st1 i1 spec1 ->
    states_related syms st1 st2 ->
    cinsn_equiv syms i1 i2 ->
    (forall st1' st2', states_related syms st1' st2' -> spec1 st1' -> spec2 st2') ->
    ctrl1 (label:=nat) st2 i2 spec2.
  Proof.
    cbv [ctrl1 cinsn_equiv err option_bind proof_semantics]; intros.
    destruct st1, st2; related_states_hammer.
  Qed.

  (* prove that run1 on related states produces a related state *)
  Lemma link_run1 fns prog syms st1 st2 spec1 spec2 :
      link fns = Ok prog ->
      link_symbols fns = Ok syms ->
      states_related syms st1 st2 ->
      (forall st1' st2',
          states_related syms st1' st2' ->
          spec1 st1' ->
          spec2 st2') ->
      run1 (fetch:=fetch_ctx fns) st1 spec1 ->
      run1 (fetch:=fetch prog) st2 spec2.
  Proof.
    cbv [run1].
    destruct st1, st2; cbn [states_related]; try contradiction; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : fetch_ctx _ _ = Some _ |- _ => eapply link_fetch in H; [ | eassumption .. ]
        | H : forall st1' st2',
            states_related _ st1' st2' ->
              spec1 st1' ->
              spec2 st2' |- spec2 _ =>
            eapply H; eauto; cbv [states_related]; ssplit; solve [eauto]
        | _ => progress subst
        end; [ ].
    eexists; ssplit; [ eauto | ].
    cbv [insn_equiv] in *.
    destruct_one_match; destruct_one_match_hyp; subst; try contradiction; [ | ].
    { (* straightline case *)
      eapply strt1_weaken; [ eassumption | ].
      cbv beta; intros.
      related_states_hammer. }
    { (* ctrl1 case *)
      eapply ctrl1_weaken; try eassumption; [ ].
      related_states_hammer. ssplit; related_states_hammer. }
  Qed.

  Lemma link_eventually_run1 fns prog syms st1 st2 spec1 spec2 :
      link fns = Ok prog ->
      link_symbols fns = Ok syms ->
      (forall st1' st2',
          states_related syms st1' st2' ->
          spec1 st1' ->
          spec2 st2') ->
      states_related syms st1 st2 ->
      eventually (run1 (fetch:=fetch_ctx fns)) spec1 st1 ->
      eventually (run1 (fetch:=fetch prog)) spec2 st2.
  Proof.
    intros. generalize dependent st2.
    let H := lazymatch goal with H : eventually _ _ _ |- _ => H end in
    induction H; intros; [ solve [eauto using eventually_done] | ].    
    eapply eventually_step; [ | solve [eauto] ].
    eapply link_run1; eauto.      
  Qed.

  Lemma link_symbols_name fns1 fns2 fn name syms :
    link_symbols (fns1 ++ fn :: fns2) = Ok syms ->
    name = fst (fst fn) ->
    map.get syms name = Some (program_size 0%nat fns1).
  Proof.
    cbv [link_symbols]; err_simpl; intros; subst; [ | congruence ].
    destruct_products; cbn [fst snd] in *.
    lazymatch goal with H : inl _ = inl _ |- _ => inversion H; clear H; subst end.
    eauto using link_symbols'_name.
  Qed.

  (* Theorem that connects run1 with a ctx to run1 with a program *)
  Lemma link_exits' :
    forall fns prog syms start_fn start_name n start_pc regs wregs flags dmem spec err_spec,
      (* ...if `prog` is the result of a successful `link fns`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...and `start_fn` is in the list... *)
      nth_error fns n = Some start_fn ->
      (* ...and `start_pc` is the global offset... *)
      start_pc = program_size 0%nat (firstn n fns) ->
      (* ...and `start_name is the name of the starting function... *)
      start_name = fst (fst start_fn) ->
      (* ...and the pre-link version satisfies the spec... *)
      exits (fetch:=fetch_ctx fns) start_name regs wregs flags dmem [] [] spec err_spec ->
      (* ...the program satisfies the spec. *)
      exits (fetch:=fetch prog) start_pc regs wregs flags dmem [] [] spec err_spec.
  Proof.
    cbv [exits]; intros.
    assert (In start_fn fns) by (eauto using nth_error_In).
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : nth_error _ _ = Some _ |- _ => apply nth_error_split in H
           | _ => progress subst
           end.
    eapply link_eventually_run1; eauto; [ | ].
    { cbv beta; intros.
      cbv [states_related] in *.
      related_states_hammer. }
    { cbv beta; intros.
      cbv [states_related]; ssplit; related_states_hammer.
      eapply link_symbols_name; [ | reflexivity .. ].
      rewrite List.firstn_app_l by lia.
      eauto. }
  Qed.

  (* like `find` except returns the index of the match *)
  Definition find_index {A} (f : A -> bool) (l : list A) : option nat :=    
    find (fun idx =>
            match nth_error l idx with
            | Some a => f a
            | None => false
            end)
      (seq 0 (length l)).

  Definition find_global_offset (fns : list function) (name : string) : option nat :=
    match find_index (fun fn => String.eqb name (fst (fst fn))) fns with
    | Some idx => Some (program_size 0%nat (firstn idx fns))
    | None => None
    end.

  Lemma find_app :
    forall {A} (f : A -> bool) l1 l2,
      find f (l1 ++ l2) = match find f l1 with
                          | Some x => Some x
                          | None => find f l2
                          end.
  Proof.
    induction l1; intros; [ reflexivity | ].
    cbn [app find]. destruct_one_match; eauto.
  Qed.

  Lemma find_map :
    forall {A B} (f : B -> bool) (g : A -> B) l,
      find f (List.map g l) = option_map g (find (fun a => f (g a)) l).
  Proof.
    cbv [option_map].
    induction l; cbn [find List.map]; intros; [ congruence | ].
    destruct_one_match_hyp; destruct_one_match;
      repeat lazymatch goal with
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | _ => first [ solve [eauto] | congruence ]
        end.
  Qed.

  Lemma find_map_inv :
    forall {A B} (f : B -> bool) (g : A -> B) l b,
      find f (List.map g l) = Some b ->
      exists a,
        find (fun a => f (g a)) l = Some a
        /\ g a = b.
  Proof.
    induction l; cbn [find List.map]; intros; [ congruence | ].
    destruct_one_match_hyp;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : Some _ = Some _ |- _ => inversion H; clear H; subst
        | H : find _ (List.map _ _) = Some _ |- _ => apply IHl in H
        | _ => solve [eauto]
        end.
  Qed.

  Lemma program_size_add :
    forall fns start,
      fold_left
        (fun offset (fn : function) => (offset + length (snd fn))%nat)
        fns start = (fold_left
                       (fun offset (fn : function) => (offset + length (snd fn))%nat)
                       fns 0 + start)%nat.
  Proof.
    induction fns; cbn [fold_left]; intros; [ lia | ].
    rewrite !(IHfns (_ + _)%nat). lia.
  Qed.

  Lemma program_size_equiv :
    forall fns1 fns2 fns3 fns4 a b start,
      program_size start fns1 = program_size start fns2 ->
      fns1 ++ a :: fns3 = fns2 ++ b :: fns4 ->
      (0 < length (snd a))%nat ->
      (0 < length (snd b))%nat ->
      a = b.
  Proof.
    cbv [program_size].
    induction fns1; destruct fns2; cbn [app fold_left]; intros; subst;
      repeat lazymatch goal with
        | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
        | H : ?start = fold_left _ _ (?start + _)%nat |- _ =>
            rewrite program_size_add in H; lia
        | H : fold_left _ _ (?start + _)%nat = ?start |- _ =>
            rewrite program_size_add in H; lia
        | |- ?x = ?x => reflexivity
        | _ => solve [eauto]
        end.    
  Qed.

  Lemma link_symbols'_app :
    forall fns1 fns2 start_syms start_offset end_offset syms,
      link_symbols' start_syms start_offset (fns1 ++ fns2) = Ok (syms, end_offset) ->
      exists syms1 end_offset1,
        link_symbols' start_syms start_offset fns1 = Ok (syms1, end_offset1)
        /\ link_symbols' syms1 end_offset1 fns2 = Ok (syms, end_offset).
  Proof.
    induction fns1; cbn [app]; intros; [ do 2 eexists; ssplit; [ reflexivity | eauto ] | ].
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               apply link_symbols'_inv in H
           | H : link_symbols' _ _ (_ ++ _) = Ok _ |- _ =>
               apply IHfns1 in H
           | _ => progress subst
           end.    
    erewrite link_symbols'_step by eauto.
    eauto.
  Qed.

  Lemma link_symbols'_no_dup' :
    forall fns start_syms start_offset end_offset syms fn1 fn2 n1 n2,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      nth_error fns n1 = Some fn1 ->
      nth_error fns n2 = Some fn2 ->
      (n1 < n2)%nat ->
      fst (fst fn1) <> fst (fst fn2).
  Proof.
    intros. intro; subst.
    repeat lazymatch goal with 
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : nth_error (_ ++ _) _ = _ |- _ => rewrite nth_error_app2 in H by lia
           | H : nth_error (_ :: _) _ = Some _ |- _ =>
               rewrite nth_error_cons in H; destruct_one_match_hyp; [ lia | ]
           | H : nth_error _ n1 = Some _ |- _ =>
               apply List.nth_error_split in H
           | H : nth_error _ ?n = Some _, H' : _ = S ?n |- _ =>
               apply List.nth_error_split in H
           | H : link_symbols' _ _ (_ ++ _) = Ok _ |- _ =>
               apply link_symbols'_app in H
           | H : link_symbols' _ _ (_ :: _) = Ok _ |- _ =>
               apply link_symbols'_inv in H
           | _ => progress (cbn [fst snd] in *; subst)
           end.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : link_symbols_for_function _ fn1 = _ |- _ =>
               apply link_symbols_for_function_name in H
           | H : link_symbols_for_function (?syms, ?off) fn2 = _,
               H' : map.get ?syms _ = Some _ |- _ =>
               eapply link_symbols_for_function_name_fail with (fn:=fn2) (start_offset:=off) in H';
               [ | solve [eauto] ]
           | H : link_symbols' ?syms _ _ = _, H' : map.get ?syms _ = Some _ |- _ =>
               eapply link_symbols'_no_overwrite in H; [ | solve [eauto] .. ]
           | _ => progress (cbn [fst snd] in *; subst)
           end.
    congruence.
  Qed.

  Lemma link_symbols'_no_dup :
    forall fns start_syms start_offset end_offset syms fn1 fn2,
      link_symbols' start_syms start_offset fns = Ok (syms, end_offset) ->
      In fn1 fns ->
      In fn2 fns ->
      fst (fst fn1) = fst (fst fn2) ->
      fn1 = fn2.      
  Proof.
    intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : In _ _ |- _ => apply In_nth_error in H
           end.
    lazymatch goal with
    | H1 : nth_error fns ?n1 = Some fn1,
        H2 : nth_error fns ?n2 = Some fn2 |- _ =>
        destr (n1 <? n2)%nat;
        [ | destr (n2 <? n1)%nat;
            [ | assert (n1 = n2) by lia; subst ] ]
    end; lazymatch goal with
         | H : (_ < _)%nat |- _ => eapply link_symbols'_no_dup' in H; eauto; congruence
         | _ => congruence
         end.
  Qed.

  Lemma link_symbols_no_dup :
    forall fns syms fn1 fn2,
      link_symbols fns = Ok syms ->
      In fn1 fns ->
      In fn2 fns ->
      fst (fst fn1) = fst (fst fn2) ->
      fn1 = fn2.      
  Proof.
    cbv [link_symbols].
    intros. err_simpl. destruct_products.
    eapply link_symbols'_no_dup; eauto.    
  Qed.

  Lemma find_ext {A} (f g : A -> bool) l (Hext : forall a, f a = g a) :
    find f l = find g l.
  Proof.
    induction l; cbn [find]; intros; [ reflexivity | ].
    rewrite Hext, IHl; reflexivity.
  Qed.

  Lemma find_index_cons {A} (f : A -> bool) l a :
      find_index f (a :: l) = if f a then Some 0%nat else option_map S (find_index f l).
  Proof.
    cbv [find_index]. cbn [length].
    rewrite <-cons_seq, <-seq_shift.
    cbn [find nth_error]. destruct_one_match; [ reflexivity | ].    
    rewrite find_map; reflexivity.
  Qed.

  Lemma find_index_Some :
    forall {A} (f : A -> bool) l i,
      find_index f l = Some i ->
      exists a,
        nth_error l i = Some a
        /\ f a = true.
  Proof.
    induction l; intros.
    { cbn [find_index length nth_error seq find] in *. congruence. }
    { rewrite find_index_cons in *. cbv [option_map] in *.
      repeat lazymatch goal with
             | H : Some _ = Some _ |- _ => inversion H; clear H; subst
             | H : None = Some _ |- _ => congruence
             | H : context [match ?x with _ => _ end] |- _ => destruct_one_match_hyp
             | _ => first [ progress (cbn [nth_error] in *; subst)
                          | solve [eauto] ]
             end. }    
  Qed.

  Lemma find_global_offset_correct' :
    forall fns syms fn name offset,
      In fn fns ->
      link_symbols fns = Ok syms ->
      find_global_offset fns name = Some offset ->
      name = fst (fst fn) ->
      exists n,
        nth_error fns n = Some fn
        /\ offset = program_size 0%nat (firstn n fns).
  Proof.
    cbv [find_global_offset]. intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           | H : None = Some _ |- _ => congruence
           | H : find_index _ _ = Some _ |- _ => apply find_index_Some in H
           | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
           | H : nth_error _ _ = Some ?fn, H' : fst (fst _) = fst (fst ?fn) |- _ =>
               eapply link_symbols_no_dup in H'; eauto using nth_error_In; subst; eauto
           | _ => first [ progress subst | destruct_one_match_hyp ]
           end.
  Qed.

  Lemma find_global_offset_correct :
    forall fns syms name offset,
      link_symbols fns = Ok syms ->
      find_global_offset fns name = Some offset ->
      exists fn n,
        nth_error fns n = Some fn
        /\ name = fst (fst fn)
        /\ In fn fns
        /\ offset = program_size 0%nat (firstn n fns).
  Proof.
    cbv [find_global_offset]. intros.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           | H : None = Some _ |- _ => congruence
           | H : find_index _ _ = Some _ |- _ => apply find_index_Some in H
           | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
           | _ => first [ progress subst | destruct_one_match_hyp ]
           end.
    do 2 eexists; ssplit; eauto using nth_error_In.    
  Qed.

  (* Theorem that connects run1 with a ctx to run1 with a program *)
  Lemma link_exits :
    forall fns prog syms start_name start_pc regs wregs flags dmem spec err_spec,
      (* ...if `prog` is the result of a successful `link fns`... *)
      link fns = Ok prog ->
      (* ..and `syms` is the symbol table for `fns`... *)
      link_symbols fns = Ok syms ->
      (* ...and `start_pc` is the global offset of `start_name`... *)
      find_global_offset fns start_name = Some start_pc ->
      (* ...and the pre-link version satisfies the spec... *)
      exits (fetch:=fetch_ctx fns) start_name regs wregs flags dmem [] [] spec err_spec ->
      (* ...the program satisfies the spec. *)
      exits (fetch:=fetch prog) start_pc regs wregs flags dmem [] [] spec err_spec.
  Proof.
    cbv [exits]; intros.
    lazymatch goal with H : find_global_offset _ _ = Some _ |- _ =>
                          eapply find_global_offset_correct in H; [ | solve [eauto] ] end.
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | _ => progress subst
           end.
    pose proof (link_correct _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    repeat lazymatch goal with
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end.
    eapply link_eventually_run1; eauto; [ | ].
    { cbv beta; intros.
      cbv [states_related] in *.
      related_states_hammer. }
    { cbv beta; intros.
      cbv [states_related]; ssplit; related_states_hammer.
      repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : nth_error _ _ = Some ?fn |- map.get syms (fst (fst ?fn)) = _ =>
                 apply nth_error_split in H
             | _ => progress subst
             end.
      erewrite link_symbols_name by eauto.
      rewrite List.firstn_app_l by lia.
      reflexivity. }
  Qed.
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

    Lemma only_differ_subset (m1 m2 : map.rep (map:=map)) s1 s2 :
      PropSet.subset s1 s2 ->
      map.only_differ m1 s1 m2 ->
      map.only_differ m1 s2 m2.
    Proof using Type.
      clear key_eqb key_eqb_spec.
      intros. cbv [map.only_differ PropSet.elem_of PropSet.subset] in *.
      intro k.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : forall x : K, _ |- _ => specialize (H k)
             | _ => tauto
             end.
    Qed.

    Lemma only_differ_same (m : map.rep (map:=map)) s :
      map.only_differ m s m.
    Proof using Type. right; reflexivity. Qed.
  End __.
End map.


Section Clobbers.
  Context {K V} {map : map.map K V} {map_ok : map.ok map}.
  Context {key_eqb : K -> K -> bool}
    {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

  Definition clobbers (l : list K) (m m' : map.rep (map:=map)) : Prop :=
    map.only_differ m (PropSet.of_list l) m'.

  Lemma clobbers_step_in l k v r1 r2 :
    clobbers l r1 r2 ->
    In k l ->
    clobbers l r1 (map.put r2 k v).
  Proof.
    cbv [clobbers PropSet.of_list]; intros.
    intro k'; cbv [map.only_differ PropSet.elem_of] in *.
    lazymatch goal with H : forall k : K, _ |- _ => specialize (H k') end.
    destr (key_eqb k k'); rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
    all:tauto.
  Qed.

  Lemma clobbers_step l k v r1 r2 :
    clobbers l r1 r2 ->
    clobbers (k :: l) r1 (map.put r2 k v).
  Proof.
    cbv [clobbers PropSet.of_list]; intros.
    intro k'; cbv [map.only_differ PropSet.elem_of] in *. cbn [In].
    lazymatch goal with H : forall k : K, _ |- _ => specialize (H k') end.
    destr (key_eqb k k'); rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
    all:tauto.
  Qed.

  Lemma clobbers_not_in l r1 r2 x v :
    clobbers l r1 r2 ->
    map.get r1 x = Some v ->
    ~ (In x l) ->
    map.get r2 x = Some v.
  Proof.
    cbv [clobbers map.only_differ PropSet.of_list PropSet.elem_of]; intros.
    lazymatch goal with H : forall x : K, _ \/ _ |- _ =>
                          destruct (H ltac:(eassumption)) end.
    all:try tauto; congruence.
  Qed.

  Lemma clobbers_trans :
    forall l1 l2 r1 r2 r3,
      clobbers l1 r1 r2 ->
      clobbers l2 r2 r3 ->
      clobbers (l1 ++ l2) r1 r3.
  Proof.
    cbv [clobbers]; intros.
    eapply map.only_differ_trans; eauto; [ ].
    rewrite PropSet.of_list_app_eq. reflexivity.
  Qed.

  Lemma clobbers_trans_dedup l1 l2 l3 r1 r2 r3 :
      clobbers l1 r1 r2 ->
      clobbers l2 r2 r3 ->
      l3 = List.dedup key_eqb (l1 ++ l2) ->
      clobbers l3 r1 r3.
  Proof.
    intros; subst.
    eapply map.only_differ_subset;
      [ | eapply map.only_differ_trans; eauto; reflexivity ].
    cbv [PropSet.of_list PropSet.subset PropSet.union PropSet.elem_of].
    intros. rewrite <-List.dedup_preserves_In.
    auto using in_or_app.
  Qed.

  Lemma clobbers_incl l1 l2 r1 r2 :
    clobbers l1 r1 r2 ->
    incl l1 l2 ->
    clobbers l2 r1 r2.
  Proof.
    cbv [incl clobbers map.only_differ PropSet.elem_of PropSet.of_list].
    intros; subst. repeat lazymatch goal with H : forall x : K, _ |- _ =>
                                                specialize (H ltac:(eassumption)) end.
    intuition idtac.
  Qed.
End Clobbers.

Ltac solve_map_step t :=
  first [ rewrite map.get_put_diff by t
        | rewrite map.get_put_same by t                       
        | reflexivity
        | eassumption
        | lazymatch goal with
          | H : map.get ?m ?k = _ |- context [map.get ?m ?k] =>
              rewrite H end
        | lazymatch goal with m := _ : map.rep |- _ =>
                                lazymatch goal with |- context [m] => subst m end end
    ].
Ltac solve_map := repeat (solve_map_step ltac:(congruence)).

(* Helper lemmas for proving things about programs. *)
Section Helpers.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 word32} {mem_ok : map.ok mem}.

  Definition gpr_has_value (regs : regfile) (r : gpr) (v : word32) : Prop :=
    read_gpr regs r (eq v).

  Lemma fetch_weaken_run1
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
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
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
    forall st P,
      eventually (run1 (fetch:=fetch1)) P st ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      eventually (run1 (fetch:=fetch2)) P st.
  Proof.
    induction 1; intros; [ auto using eventually_done | ].
    eapply eventually_step; eauto using fetch_weaken_run1.
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
    {label : Type}
    {fetch1 : label * nat -> option insn}
    {fetch2 : label * nat -> option insn} :
    forall dst pc (regs : regfile) wregs flags dmem cstack lstack spec post,
      fetch2 pc = Some (Control (Jal x1 dst)) ->
      (length cstack < 8)%nat ->
      returns (fetch:=fetch1) dst regs wregs flags dmem (advance_pc pc :: cstack) lstack spec ->
      (forall dst i, fetch1 dst = Some i -> fetch2 dst = Some i) ->
      (forall regs wregs flags dmem,
          spec regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch2))
            post (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch2)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    cbv [returns]; intros.
    cbn [hd_error] in *.
    eapply eventually_step.
    { cbv [run1]; intros. eexists; split; [ eassumption | ].
      cbv iota. cbn [ctrl1 call_stack_push set_pc].
      destruct_one_match; try lia; apply eq_refl. }
    intros; subst.
    eapply eventually_trans;
      [ eapply fetch_weaken; eauto | intro st; destruct st; try contradiction ].
    intros; repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end. subst.
    cbn [tl]. eauto.
  Qed.
    
  Lemma eventually_invariant {label : Type} {fetch : label * nat -> option insn} :
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

  Definition get_lstack {label : Type} (st : otbn_state)
    : option (list (label * nat * nat)) :=
    match st with
    | otbn_busy _ _ _ _ _ _ lstack => Some lstack
    | _ => None
    end.

  (* Loop invariant helper lemma. Note: `invariant i` should hold on
     the state the loop has when it reaches the end of the loop body
     in the `i`th iteration from last, so e.g. `invariant 0` should
     hold at the very end of the loop. *)
  Lemma loop_invariant
    {label : Type} {fetch : label * nat -> option insn} :
    forall (invariant : nat -> regfile -> wregfile -> flagfile -> mem -> Prop)
           (end_pc : label * nat)
           iters pc r v (regs : regfile) wregs flags dmem cstack lstack post,
      fetch pc = Some (Control (Loop r)) ->
      fetch end_pc = Some (Control LoopEnd) ->
      gpr_has_value regs r v ->
      Z.of_nat iters = word.unsigned v ->
      (length lstack < 8)%nat ->
      iters <> 0%nat ->
      invariant iters regs wregs flags dmem ->
      (* invariant step condition; if `invariant` holds at start, we reach end *)
      (forall i regs wregs flags dmem,
          (0 <= i <= iters)%nat ->
          invariant (S i) regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch))
          (fun st => (exists regs wregs flags dmem,
                         invariant i regs wregs flags dmem
                         /\ st = match i with
                                 | S i => otbn_busy (advance_pc pc) regs wregs flags dmem cstack
                                            ((advance_pc pc, i) :: lstack)
                                 | O => otbn_busy (advance_pc end_pc)
                                          regs wregs flags dmem cstack lstack
                                 end)
                     \/ post st)
          (otbn_busy (advance_pc pc) regs wregs flags dmem cstack
             ((advance_pc pc, i) :: lstack))) ->
      (forall regs wregs flags dmem,
          invariant 0%nat regs wregs flags dmem ->
          eventually (run1 (fetch:=fetch)) post
            (otbn_busy (advance_pc end_pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    cbv [loop_start]; intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct iters; [ lia | ].    
    eapply eventually_step.
    { cbn [run1]. eexists; ssplit; [ eassumption | ].
      cbv iota. cbn [ctrl1 read_gpr_from_state].
      eapply read_gpr_weaken; [ eassumption | ].
      intros; cbv [loop_start]. ssplit; [ lia .. | ].
      subst.
      lazymatch goal with H : Z.of_nat _ = word.unsigned ?v |- context [word.unsigned ?v] =>
                            rewrite <-H end.
      rewrite Nat2Z.id.
      destruct_one_match; try lia; eapply eq_refl. }
    intros; subst.
    eapply eventually_invariant
      with (iters := S iters)
           (invariant :=
              fun i st =>
                (exists regs wregs flags dmem,
                    invariant i regs wregs flags dmem
                    /\ st = match i with
                            | S i => otbn_busy (advance_pc pc) regs wregs flags dmem cstack
                                       ((advance_pc pc, i) :: lstack)
                            | O => otbn_busy (advance_pc end_pc) regs wregs flags dmem cstack lstack
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

  Lemma eventually_beq {label : Type} {fetch : label * nat -> option insn}:
    forall pc dst r1 r2 regs wregs flags dmem cstack lstack v1 v2 post,
      fetch pc = Some (Control (Beq r1 r2 dst)) ->
      gpr_has_value regs r1 v1 ->
      gpr_has_value regs r2 v2 ->
      (* branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (dst, 0%nat) regs wregs flags dmem cstack lstack)) ->
      (* no-branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros.
    destr (word.eqb v1 v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        rewrite word.eqb_eq by reflexivity.
        cbv [set_pc]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_bne {label : Type} {fetch : label * nat -> option insn}:
    forall pc dst r1 r2 regs wregs flags dmem cstack lstack v1 v2 post,
      fetch pc = Some (Control (Bne r1 r2 dst)) -> 
      gpr_has_value regs r1 v1 ->
      gpr_has_value regs r2 v2 ->
      (* branch case *)
      (v1 <> v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (dst, 0%nat) regs wregs flags dmem cstack lstack)) ->
      (* no-branch case *)
      (v1 = v2 ->
       eventually (run1 (fetch:=fetch)) post
         (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros.
    destr (word.eqb v1 v2).
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
    { eapply eventually_step.
      { cbv [run1]. eexists; ssplit; [ eassumption .. | ]. cbv [ctrl1 read_gpr_from_state].
        repeat (eapply read_gpr_weaken; [ eassumption .. | ]; intros; subst).
        destruct_one_match; try congruence; [ ]. apply eq_refl. }
      intros; subst. eauto. }
  Qed.

  Lemma eventually_loop_end {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack loop_start iters post,
      fetch pc = Some (Control LoopEnd) ->
      (match iters with
       | O => eventually (run1 (fetch:=fetch)) post
                (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)
       | S iters => eventually (run1 (fetch:=fetch)) post
                      (otbn_busy loop_start regs wregs flags dmem cstack
                         ((loop_start, iters) :: lstack))
       end) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack ((loop_start, iters) :: lstack)).
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

  Lemma eventually_ret {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack ret_pc post,
      fetch pc = Some (Control Ret) ->
      hd_error cstack = Some ret_pc ->
      post (otbn_busy ret_pc regs wregs flags dmem (tl cstack) lstack) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbn [ctrl1 call_stack_pop]. eexists; ssplit; [ eassumption .. | ].
      apply eq_refl. }
    intros; subst. eauto using eventually_done.
  Qed.

  Lemma eventually_ecall {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack post,
      fetch pc = Some (Control Ecall) ->
      post (otbn_done pc dmem) ->
      eventually (run1 (fetch:=fetch)) post
        (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbn [ctrl1 program_exit]. eassumption. }
    intros; subst. eauto using eventually_done.
  Qed.

  (* TODO: maybe strt1 should return a function args -> result? need
     more detail here, need to express new map *)
  Lemma eventually_straightline
    {label : Type} {fetch : label * nat -> option insn}:
    forall pc regs wregs flags dmem cstack lstack i post,
      fetch pc = Some (Straightline i) ->
      strt1 regs wregs flags dmem i
        (fun regs wregs flags dmem =>
           eventually (run1 (fetch:=fetch)) post
             (otbn_busy (advance_pc pc) regs wregs flags dmem cstack lstack)) ->
      eventually (run1 (fetch:=fetch)) post (otbn_busy pc regs wregs flags dmem cstack lstack).
  Proof.
    intros. eapply eventually_step.
    { cbv [run1]. eexists; ssplit; [ eassumption .. | ].
      cbv iota. cbv [update_state set_pc]. eassumption. }
    intros; subst. eauto.
  Qed.

  Lemma is_valid_addr_iff addr :
    is_valid_addr addr = true <-> (word.unsigned addr mod 4 = 0
                                   /\ word.unsigned addr + 4 < DMEM_BYTES).
  Proof.
    cbv [is_valid_addr]. rewrite Bool.andb_true_iff, word.unsigned_eqb, Z.eqb_eq.
    rewrite word.unsigned_and, !word.unsigned_of_Z_nowrap by lia.
    rewrite Z.land_ones with (n:=2) by lia. change (2^2) with 4.
    pose proof Z.mod_pos_bound (word.unsigned addr) 4 ltac:(lia).
    cbv [word.wrap]. rewrite Z.mod_small; lia.
  Qed.

  Lemma is_valid_addr_0 : is_valid_addr (word.of_Z 0) = true.
  Proof.
    cbv [is_valid_addr]. apply Bool.andb_true_iff. ssplit.
    { apply word.eqb_eq, word.unsigned_inj.
      rewrite word.unsigned_and, !word.unsigned_of_Z_nowrap by lia.
      cbv [Z.land word.wrap]. rewrite Z.mod_small; lia. }
    { cbv [DMEM_BYTES]. rewrite word.unsigned_of_Z_nowrap by lia.
      lia. }
  Qed.

  Lemma is_valid_addr_add addr offset :
    is_valid_addr addr = true ->
    offset mod 4 = 0 ->
    0 <= offset ->
    0 <= word.unsigned addr + offset + 4 < DMEM_BYTES ->
    is_valid_addr (word.add addr (word.of_Z offset)) = true.
  Proof.
    cbv [is_valid_addr DMEM_BYTES]. rewrite !Bool.andb_true_iff. intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : word.eqb ?x ?y = true |- _ =>
               rewrite word.unsigned_eqb in H
           | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
           | H : word.ltu ?x ?y = true |- _ =>
               destruct (word.ltu_spec x y); [ | congruence ]; clear H;
               rewrite ?word.unsigned_of_Z_nowrap in * by lia
           end.
    pose proof (word.unsigned_range addr).
    ssplit.
    { apply word.eqb_eq, word.unsigned_inj.
      rewrite word.unsigned_and, word.unsigned_add, !word.unsigned_of_Z_nowrap in * by lia.
      cbv [word.wrap] in *. rewrite (Z.mod_small (_ + _)) by lia.
      rewrite !(Z.land_ones _ 2) in * by lia. change (2 ^ 2) with 4 in *.
      repeat lazymatch goal with
             | H : context [(?x mod 4) mod _] |- _ =>
                 rewrite (Z.mod_small (x mod 4) _) in H;
                 [ | pose proof (Z.mod_pos_bound x 4 ltac:(lia)); lia ]
             | |- context [(?x mod 4) mod _] =>
                 rewrite (Z.mod_small (x mod 4) _);
                 [ | pose proof (Z.mod_pos_bound x 4 ltac:(lia)); lia ]
             end.
      rewrite Z.add_mod by lia.
      repeat lazymatch goal with
             | H : ?x = 0 |- context[?x] => rewrite H
             | H : 0 = ?x |- context[?x] => rewrite <-H
             end.
      rewrite Z.mod_0_l by lia.
      reflexivity. }
    { rewrite word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
      apply Z.ltb_lt.
      cbv [word.wrap]. rewrite Z.mod_small by lia.
      lia. }
  Qed.

  Definition start_state : otbn_state :=
    otbn_busy (0%nat, 0%nat) map.empty map.empty map.empty map.empty [] [].
End Helpers.


Ltac zsimplify_step :=
  lazymatch goal with
  | |- context [_ + 0] => rewrite Z.add_0_r
  | |- context [0 + _] => rewrite Z.add_0_l
  | |- context [_ - 0] => rewrite Z.sub_0_r
  | |- context [?x - ?x] => rewrite Z.sub_diag
  | |- context [_ * 0] => rewrite Z.mul_0_r
  | |- context [0 * _] => rewrite Z.mul_0_l
  | |- context [_ * 1] => rewrite Z.mul_1_r
  | |- context [1 * _] => rewrite Z.mul_1_l
  | |- context [0 mod _] => rewrite Z.mod_0_l by lia
  | |- context [?x mod ?x] => rewrite (Z.mod_same x) by lia
  | |- context [Z.of_nat (Z.to_nat _)] => rewrite Z2Nat.id by lia
  | |- context [Z.to_nat (Z.of_nat _)] => rewrite Nat2Z.id by lia
  | |- context [Z.of_nat 0] => change (Z.of_nat 0) with 0
  | |- context [Z.of_nat 1] => change (Z.of_nat 1) with 1
  | _ => progress Z.push_pull_mod
  end.
Ltac zsimplify := repeat zsimplify_step.


(* Separation logic defs. This section is copied directly from
   bedrock2 (copied to avoid introducing a bedrock2 dependency). *)
Section Sep.
  Context {key value} {map : map.map key value}.
  Definition emp (P : Prop) := fun m : map => m = map.empty /\ P.
  Definition sep (p q : map -> Prop) m :=
    exists mp mq, map.split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m : map => m = map.put map.empty k v.
End Sep.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := sep (at level 40, left associativity) : sep_scope.

Section SepProofs.
  Context {key value} {map : map.map key value} {map_ok : map.ok map}.
  Context {key_eqb : key -> key -> bool}
    {key_eq_dec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}.

  Lemma sep_comm p q (m : map) :
    sep p q m -> sep q p m.
  Proof.
    cbv [sep]; intros [mp [mq ?]]. intros. exists mq, mp.
    cbv [map.split] in *.
    repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    subst; ssplit; eauto; [ | ].
    { eapply map.putmany_comm; eauto. }
    { eapply map.disjoint_comm; eauto. }
  Qed.

  Lemma sep_weaken_l p q r (m : map) :
    sep p q m -> (forall m, p m -> r m) -> sep r q m.
  Proof.
    cbv [sep]; intros [mp [mq ?]]. intros. exists mp, mq.
    repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    ssplit; eauto.
  Qed.

  Lemma sep_weaken_r p q r (m : map) :
    sep p q m -> (forall m, q m -> r m) -> sep p r m.
  Proof.
    intros. apply sep_comm. eapply sep_weaken_l; [ apply sep_comm | .. ]; eauto.
  Qed.

  Lemma sep_exists_l p q (m : map) :
    sep p q m -> exists m, p m.
  Proof.
    cbv [sep]; intros [mp [mq ?]]. intros. exists mp.
    repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    ssplit; eauto.
  Qed.

  Lemma sep_exists_r p q (m : map) :
    sep p q m -> exists m, q m.
  Proof.
    intros. eapply sep_exists_l; [ apply sep_comm | .. ]; eauto.
  Qed.

End SepProofs.

(* Additional separation-logic definitions. *)
Section SepDefs.
  Context {word32 : word.word 32} {word256 : word.word 256} {mem : map.map word32 word32}.

  Definition bignum (addr : word32) (v : word256) (m : mem) : Prop :=
    bignum_load m addr (eq v).

  Definition buf (addr : word32) (n : nat) (m : mem) : Prop :=
    is_valid_addr addr = true
    /\ 0 <= word.unsigned addr + (4 * Z.of_nat n) < DMEM_BYTES.

  Section Proofs.
    Context {word32_ok : word.ok word32} {word256_ok : word.ok word256} {mem_ok : map.ok mem}.
    Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
    
    Lemma bignum_clear dmem addr v R :
      (bignum addr v * R)%sep dmem ->
      (buf addr 8 * R)%sep dmem.
    Proof.
      intros; eapply sep_weaken_l; eauto.
      cbv [bignum bignum_load buf read_mem err option_bind proof_semantics]; intros.
      repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : False |- _ => contradiction H
             | |- True => trivial
             | |- context [word.add (word.add ?x (word.of_Z ?y)) (word.of_Z 4)] =>
                 rewrite <-(word.add_assoc x (word.of_Z y) (word.of_Z 4));
                 rewrite <-(word.ring_morph_add y 4);
                 cbn [Z.add Pos.add Pos.succ]
             | H : context [word.unsigned (word.of_Z _)] |- _ =>
                 rewrite word.unsigned_of_Z_nowrap in H by (cbv [DMEM_BYTES]; lia)
             | H : if ?x then _ else _ |- _ => destr x
             end.
      pose proof (word.unsigned_range addr).
      ssplit; [ reflexivity | lia | ].
      rewrite word.unsigned_add, word.unsigned_of_Z_nowrap in * by lia.
      cbv [word.wrap DMEM_BYTES] in *.
      rewrite !(Z.mod_small (word.unsigned addr + _)) in * by lia.
      lia.
    Qed.

    Lemma buf_valid_addr start size offset :
      (exists m, buf start size m) ->
      0 <= offset < 4 * Z.of_nat size ->
      offset mod 4 = 0 ->
      is_valid_addr (word.add start (word.of_Z offset)) = true.
    Proof.
      intros [? [? ?]]. intros; subst.
      apply is_valid_addr_add; eauto; try lia; [ ].
      rewrite is_valid_addr_iff in *.
      pose proof (word.unsigned_range start).
      repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
      let x := lazymatch goal with
               | H : context [ word.unsigned start + ?x < DMEM_BYTES] |- _ => x end in        
      destr (offset <=? x - 4); [ lia | ];
      assert (offset = x - 3 \/ offset = x - 2 \/ offset = x - 1) by lia.
      assert (offset mod 4 <> 0); [ | lia ].
      repeat lazymatch goal with
             | H : _ \/ _ |- _ => destruct H; subst
             end.
      all:Z.push_mod.
      all:zsimplify.
      all:cbn; congruence.
    Qed.

    Lemma buf_range m n :
      forall addr,
        buf addr n m ->
        (0 < n)%nat ->
        0 <= word.unsigned addr < DMEM_BYTES - (4 * Z.of_nat n).
    Proof.
      induction n; cbn [buf]; [ lia | ]. intros.
      destruct_one_match_hyp; [ | contradiction ].
      repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
      rewrite ?word.unsigned_of_Z_nowrap in * by (cbv [DMEM_BYTES]; lia).
      destr (0 <? n)%nat.
      {
        specialize (IHn _ ltac:(eassumption) ltac:(lia)).
        rewrite word.unsigned_add in IHn.
    Qed.

    Ltac prove_word_neq :=
      lazymatch goal with
      |- not (@eq word.rep ?x ?y) =>
          apply word.eqb_false; rewrite word.unsigned_eqb;
          apply Z.eqb_neq;
          rewrite ?word.unsigned_add, ?word.unsigned_of_Z_nowrap by lia;
          cbv [word.wrap]; rewrite ?Z.mod_small; lia
      end.

    Lemma bignum_store_step m addr v :
      buf addr 8 m ->
      bignum_store m addr v (bignum addr v).
    Proof.
      intros.
      pose proof (buf_range _ _ _ ltac:(eassumption)).
      change (4 * Z.of_nat 8) with 32 in *. cbv [DMEM_BYTES] in *.
      cbv [ bignum_store bignum bignum_load write_mem read_mem
              option_bind err proof_semantics ].
      replace (is_valid_addr addr) with (is_valid_addr (word.add addr (word.of_Z 0)))
        by (rewrite word.add_0_r; reflexivity).
      repeat (erewrite buf_valid_addr;
              [ | solve [eauto using sep_exists_l] | lia | reflexivity ]).
      repeat (rewrite ?map.get_put_diff by prove_word_neq; rewrite map.get_put_same;
              eexists; ssplit; [ reflexivity .. | ]).
      cbv [bignum_combine].
      rewrite !word.unsigned_of_Z.
      apply word.unsigned_inj. rewrite word.unsigned_of_Z.
      cbv [word.wrap]. rewrite <-!Z.land_ones by lia.
      apply Z.bits_inj'. intro i. intros.
      repeat first
        [ rewrite Z.land_spec
        | rewrite Z.lor_spec
        | rewrite Z.shiftl_spec by lia
        | rewrite Z.shiftr_spec by lia
        | rewrite Z.testbit_ones by lia
        ].
      pose proof (word.unsigned_range v).
      destr (i <? 256);
        repeat
          multimatch goal with
          | |- context [Z.testbit (Z.shiftr _ _) ?i] =>
              destr (0 <=? i);
              [ try lia; rewrite Z.shiftr_spec by lia; rewrite Z.sub_simpl_r
              | try lia; rewrite Z.testbit_neg_r with (n:=i) by lia ]
          | H : ?x <= ?y |- context [Z.leb ?x ?y] => destr (x <=? y); try lia; [ ]
          | |- context [Z.ltb ?x ?y] =>  destr (x <? y); try lia; [ ]
          end.
      all:
      repeat first
        [ rewrite Bool.andb_true_l
        | rewrite Bool.andb_true_r
        | rewrite Bool.andb_false_l
        | rewrite Bool.andb_false_r
        | rewrite Bool.orb_true_l
        | rewrite Bool.orb_true_r
        | rewrite Bool.orb_false_l
        | rewrite Bool.orb_false_r
        | reflexivity
        ].
      (* should only have 256 < i case left now *)
      pose proof Z.pow_le_mono_r 2 256 i ltac:(lia) ltac:(lia).
      apply Z.testbit_false; [ lia .. | ].
      rewrite Z.div_small; [ reflexivity | ].
      lia.
    Qed.

    Lemma bignum_store_step dmem addr v R P :
      (buf addr 8 * R)%sep dmem ->
      (forall dmem, (bignum addr v * R)%sep dmem -> P dmem) ->
      bignum_store dmem addr v P.
    Proof.
      intros. cbv [bignum_store write_mem].
      erewrite buf_valid_addr with (offset:=0);
        [ | solve [eauto using sep_exists_l] | lia | reflexivity | ring ].
      repeat (erewrite buf_valid_addr; [ .. | reflexivity ];
              [ | solve [eauto using sep_exists_l] | lia | reflexivity ]).
      lazymatch goal with H : forall _, _ -> ?P _ |- ?P _ => apply H end.
      (* something for sep is needed here -- need to say that the
         split is the same as in the hypothesis *)
      rewrite ?map.get_put
    Qed.
  End Proofs.
End SepDefs.

Ltac solve_is_valid_addr :=
  lazymatch goal with
  | H : is_valid_addr ?a = true |- is_valid_addr ?a = true => exact H
  | |- is_valid_addr (word.of_Z 0) = true => apply is_valid_addr_0
  | |- is_valid_addr (word.add ?a (word.of_Z ?offset)) = true =>
      assert (is_valid_addr a = true) by solve_is_valid_addr; apply is_valid_addr_add;
      eauto; cbv[DMEM_BYTES] in *; rewrite ?word.unsigned_of_Z_nowrap by lia; lia
  end.
  

Ltac simplify_side_condition_step :=
  match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- context [if is_valid_addi_imm ?v then _ else _] =>
        replace (is_valid_addi_imm v) with true by (cbv [is_valid_addi_imm]; lia)
  | |- context [if is_valid_mem_offset ?v then _ else _] =>
        replace (is_valid_mem_offset v) with true by (cbv [is_valid_mem_offset]; lia)
  | |- context [if is_valid_addr ?a then _ else _] =>
        replace (is_valid_addr a) with true by (symmetry; solve_is_valid_addr)
  | |- context [(_ + 0)%nat] => rewrite Nat.add_0_r
  | |- context [fetch_fn (?s, _, _) (?s, _)] => rewrite fetch_fn_name by auto
  | |- match fetch_fn ?fn ?pc with _ => _ end = Some _ => reflexivity
  | |- context [fetch_fn _ _] =>
      erewrite fetch_fn_sym by
      (cbn [fst snd]; first [ congruence | solve_map ])
  | |- map.get _ _ = Some _ => solve_map
  | H : map.get ?m ?k = Some _ |- context [match map.get ?m ?k with _ => _ end] =>
      rewrite H
  | |- context [match map.get _ _ with _ => _ end] => solve_map
  | |- context [advance_pc (?dst, ?off)] =>
      change (advance_pc (dst, off)) with (dst, S off)
  | |- (_ < _) => lia
  | |- (_ <= _) => lia                                   
  | |- (_ < _)%nat => lia
  | |- (_ <= _)%nat => lia
  | |- Some _ = Some _ => reflexivity
  | _ => first [ progress
                   cbn [run1 strt1 read_gpr write_gpr ctrl1
                          read_gpr_from_state read_mem
                          set_pc update_state call_stack_pop call_stack_push
                          length hd_error tl skipn nth_error fold_left
                          fetch fetch_ctx Nat.add fst snd
                          err random option_bind proof_semantics
                          repeat_advance_pc advance_pc]
               | progress cbv [gpr_has_value write_mem]
               | eassumption ]
  end.
Ltac simplify_side_condition := repeat simplify_side_condition_step.

(* Run the linker to compute the fully linked version of a program *)
Ltac link_program fns :=
  let val := eval vm_compute in (link fns) in
    lazymatch val with
    | inl ?x => exact x
    | inr ?e => fail e
    end.

Ltac get_next_insn :=
  lazymatch goal with
  | |- eventually (run1 (fetch:=?fetch)) _ (otbn_busy ?pc _ _ _ _ _ _) =>
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
  | |- context [eventually (run1 (fetch:=?fetch)) _ (otbn_busy ?pc _ _ _ _ _ _)] =>
      let i := eval vm_compute in (fetch pc) in
        match i with
        | Some (Control (Loop _)) => find_loop_end' fetch (advance_pc pc)
        | Some (Control (Loopi _)) => find_loop_end' fetch (advance_pc pc)
        | ?x => fail "expected a loop insn at " pc ", got " x
        end
  | _ => fail "could not determine fetch and pc from goal"
  end.

(* register tracking initialize *)
Ltac track_registers_init :=
  let regs := lazymatch goal with
              | |- context [otbn_busy _ ?regs] => regs end in
  let regs' := fresh "regs" in
  let H := fresh in
  remember regs as regs' eqn:H;
  assert (clobbers [] regs regs')
    by (cbv [clobbers]; subst regs'; right; reflexivity);
  (* rewrite back in postcondition but not state *)
  rewrite H;
  lazymatch goal with
  | |- context [otbn_busy ?pc regs] =>
      replace (otbn_busy pc regs) with (otbn_busy pc regs')
      by (rewrite H; reflexivity)
  end;
  clear H.

Ltac update_clobbers k l v H :=
  first [ (let Hin := fresh in
           assert (In k l) as Hin by (cbv [In]; tauto);
           pose proof (clobbers_step_in l k v _ _ H Hin))
        | pose proof (clobbers_step l k v _ _ H) ].
Ltac update_live_registers r k v r' :=
  let Heq := fresh in
  remember (map.put r k v) as r' eqn:Heq;
  assert (map.get r' k = Some v) by (subst r'; apply map.get_put_same);
  repeat lazymatch goal with
    | H : map.get r k = Some _ |- _ => clear H
    | H : map.get r ?k = Some ?v |- _ =>
        assert (map.get r' k = Some v)
        by (subst r'; rewrite map.get_put_diff by congruence; eauto);
        clear H
    end;
  clear Heq.
  (* try clobbers_step_in first, then more generic clobbers_step *)
Ltac track_registers_update_step :=
  lazymatch goal with
  | |- context [otbn_busy _ (map.put ?regs0 ?k ?v)] =>
      (* update to small registers *)
      lazymatch goal with
      | H : @clobbers reg _ _ ?l ?regs ?regs0 |- _ =>
          let v' := fresh "v" in
          set (v':= v);
          update_clobbers k l v' H;
          let regs1 := fresh "regs" in
          update_live_registers regs0 k v' regs1;
          clear H regs0
      | _ => fail "Could not find hypothesis for clobbered GPRs"
      end
  | _ => idtac (* nothing was updated *)
  end.
Ltac track_registers_update :=
  track_registers_update_step; repeat progress track_registers_update_step.

(* use after a jump to combine the postconditions *)
Ltac track_registers_combine :=
  lazymatch goal with
  | H0 : clobbers ?l0 ?regs ?regs0,
      H1 : clobbers ?l1 ?regs0 ?regs1
    |- context [otbn_busy _ ?regs1] =>
      repeat lazymatch goal with
        | H : map.get regs0 ?r = _ |- _ =>
            try (let Hnin := fresh in
                 assert (~ In r l1) as Hnin by (cbv [In]; intuition congruence);
                 pose proof (clobbers_not_in l1 _ _ _ _ H1 H Hnin);
                 clear Hnin);
            clear H
        end;
      let l2 := (eval vm_compute in (List.dedup reg_eqb (l0 ++ l1))) in
      pose proof (clobbers_trans_dedup (key_eqb:=reg_eqb)
                    _ _ l2 _ _ _ H0 H1 ltac:(reflexivity));
      clear H0 H1; try clear regs0
  end.

Ltac check_register_tracking :=
  lazymatch goal with
  | H : clobbers _ _ ?regs0 |- context [?regs0] => idtac
  | _ => fail "cannot find register tracking; did you run track_registers_init?"
  end.

Ltac init_register_tracking_if_missing :=
  first [ check_register_tracking
        | track_registers_init ].

Ltac straightline_step :=
  init_register_tracking_if_missing;
  let i := get_next_insn in
  lazymatch i with
  | Some (Straightline _) =>
      intros; subst; eapply eventually_step;
      [ simplify_side_condition; [ .. | try eapply eq_refl]
      | intros; subst; track_registers_update ]
  | Some ?i => fail "next instruction is not straightline:" i
  | None => fail "pc is invalid?"
  end.

Ltac subst_lets_step :=
  multimatch goal with
  | x := _ |- _ => lazymatch goal with |- context [x] => subst x end
  end.
Ltac subst_lets := repeat subst_lets_step.

Module Test.
  Section __.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 word32} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  
  (* Test program : a function that adds two registers.

     start:
       addi x2, x0, 2
       addi x3, x0, 3
       jal  x1, add
       sw   x5, 0(x0)
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
        (Sw x0 x5 0 : insn) ;
        (Ecall : insn)])%string.

  Compute (link [start_fn; add_fn]).

  (* Test program : build multiplication out of addition

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

  (* Test program : add two values from memory

     start:
       lw   x2, 0(x0)
       lw   x3, 4(x0)
       jal  x1, add
       sw   x5, 0(x0)
       ecall

     add:
       add  x5, x2, x3
       ret
   *)
  Definition start_mem_fn : function :=
    ("start",
      map.empty,
      [ (Lw x2 x0 0 : insn);
        (Lw x3 x0 4 : insn);
        (Jal x1 "add" : insn);
        (Sw x0 x5 0 : insn) ;
        (Ecall : insn)])%string.

  Compute (link [mul_fn; add_fn]).

  Definition prog0 : program := ltac:(link_program [start_fn; add_fn]).

  Lemma prog0_correct :
    eventually
      (run1 (fetch:=fetch prog0))
      (fun st =>
         match st with
         | otbn_done _ dmem =>
             map.get dmem (word.of_Z 0) = Some (word.of_Z 5)
         | _ => False
         end)
      start_state.
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
    intros; subst. eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst. eapply eventually_done.
    rewrite word.add_0_r.
    solve_map. apply f_equal.
    cbv [addi_spec]. repeat destruct_one_match; try lia; [ ].    
    rewrite !word.add_0_l.
    apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z by lia.
    cbv [word.wrap]. Z.push_pull_mod. reflexivity.
  Qed.

  Lemma add_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get regs (gpreg x2) = Some a ->
      map.get regs (gpreg x3) = Some b ->
      returns
        (fetch:=fetch_ctx [add_fn])
        "add"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x5) = Some (word.add a b)
           /\ wregs' = wregs
           (* note: no guarantees about flags *)
           /\ dmem' = dmem
           /\ clobbers [gpreg x5] regs regs').
  Proof.
    cbv [add_fn returns]. intros; subst.
    track_registers_init.
    
    eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | ].
    { solve_map. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
  Qed.

  Lemma mul_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get regs (gpreg x3) = Some a ->
      map.get regs (gpreg x4) = Some b ->
      (length cstack < 8)%nat ->
      (length lstack < 8)%nat ->
      returns
        (fetch:=fetch_ctx [mul_fn; add_fn])
        "mul"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x2) = Some (word.mul a b)
           /\ wregs' = wregs
           /\ dmem' = dmem
           /\ clobbers [gpreg x2; gpreg x5] regs regs').
  Proof.
    cbv [mul_fn returns]. intros; subst. 
    repeat straightline_step.
 
    (* branch; use branch helper lemma *)
    eapply eventually_beq.
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { simplify_side_condition; reflexivity. }
    { (* case: b = 0, exit early *)
      intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
      rewrite word.mul_0_r.
      ssplit; try reflexivity; [ | ].
      { (* result value *)
        solve_map; subst_lets. cbv [addi_spec].
        destruct_one_match; try lia; [ ].
        apply f_equal. ring. }
      { eapply clobbers_incl; eauto.
        cbv [incl In]; tauto. } }
    (* case: b <> 0, proceed *)
    intros; subst.

    pose proof (word.unsigned_range b).
    assert (0 < word.unsigned b).
    { lazymatch goal with H : b <> word.of_Z 0 |- _ =>
                            apply word.unsigned_inj' in H end.
      rewrite word.unsigned_of_Z_0 in *.
      lia. }
 
    (* loop; use loop invariant lemma *)
    let loop_end_pc := find_loop_end in
    eapply loop_invariant
      with
      (end_pc:=loop_end_pc)
      (invariant :=
         fun i regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x2) = Some (word.mul a (word.sub b (word.of_Z (Z.of_nat i))))
           /\ map.get regs' (gpreg x3) = Some a
           /\ map.get regs' (gpreg x4) = Some b
           /\ wregs' = wregs
           /\ dmem' = dmem
           /\ clobbers [gpreg x2; gpreg x5] regs regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; simplify_side_condition; zsimplify; try reflexivity.
      { (* accumulator value *)
        subst_lets. apply f_equal.
        cbv [addi_spec]. destruct_one_match; try lia; [ ].
        rewrite word.of_Z_unsigned. ring. }
      { (* clobbered registers *)
        eapply clobbers_incl; eauto. cbv [incl In]; tauto. } }
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
      { apply add_correct; eauto. }
      { intros.
        rewrite fetch_ctx_weaken_cons_ne; [ eassumption | ].
        eapply fetch_fn_disjoint; eauto; [ ].
        eapply fetch_ctx_singleton_iff; eauto. }

      (* post-jump; continue *)
      cbv beta. intros; subst.
      repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
      track_registers_combine.

      repeat straightline_step.

      (* end of loop; use loop-end helper lemma *)
      eapply eventually_loop_end; [ reflexivity .. | ].
      destruct_one_match.
      { (* case: i = 0, loop ends *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ ].
        simplify_side_condition; subst_lets; zsimplify.
        cbv [addi_spec]. destruct_one_match; try lia.
        apply f_equal. ring. }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ ].
        { simplify_side_condition. subst_lets; zsimplify.
          cbv [addi_spec]. destruct_one_match; try lia.
          apply f_equal.
          replace (word.of_Z (Z.of_nat (S (S i))))
            with (word.add (word:=word32) (word.of_Z (Z.of_nat (S i))) (word.of_Z 1));
            [ ring | ].
          apply word.unsigned_inj.
          rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap, word.unsigned_of_Z by lia.
          rewrite Z.add_1_r, <-Nat2Z.inj_succ. reflexivity. } } }
 
    (* invariant implies postcondition (i.e. post-loop code) *)
    zsimplify. rewrite word.sub_0_r. intros.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : Some _ = Some _ |- _ => inversion H; clear H; subst
           end.
    simplify_side_condition.
    repeat straightline_step.
    intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; eauto.
  Qed.

  Lemma prog0_correct_prelink regs wregs flags dmem :
    exits
      (fetch:=fetch_ctx [start_fn; add_fn])
      "start"%string regs wregs flags dmem [] []
      (fun dmem' =>
         map.get dmem' (word.of_Z 0) = Some (word.of_Z 5))
      (fun errs => False).
  Proof.
    cbv [exits start_fn start_state]; intros.
    repeat straightline_step.

    eapply eventually_jump.
    { reflexivity. }
    { cbn [length]; lia. }
    { eapply add_correct; eauto. }
    { intros.
      rewrite fetch_ctx_weaken_cons_ne; [ eassumption | ].
      eapply fetch_fn_disjoint; eauto; [ | ].
      { eapply fetch_ctx_singleton_iff; eauto. }
      { cbv; intuition congruence. } }

    cbv beta. intros; subst.
    repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    track_registers_combine.

    repeat straightline_step.

    eapply eventually_ecall; ssplit; [ reflexivity .. | ].
    subst_lets. cbv [addi_spec]. repeat destruct_one_match; try lia; [ ].
    rewrite !word.add_0_l. solve_map.
    apply f_equal. apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
    reflexivity.
  Qed.

  (* check that link_run1 works by using add_fn proof to prove link_run1 program *)
  Lemma prog0_correct_postlink :
    exits
      (fetch:=fetch prog0)
      0%nat map.empty map.empty map.empty map.empty [] []
      (fun dmem' =>
         map.get dmem' (word.of_Z 0) = Some (word.of_Z 5))
      (fun errs => False).
  Proof.
    set (fns:=[start_fn; add_fn]).
    assert (link fns = inl prog0) by reflexivity.
    let x := eval vm_compute in (link_symbols [start_fn; add_fn]) in
      match x with
      | inl ?x =>
          pose (syms:=x)
      | _ => fail
      end.
    assert (link_symbols fns = inl syms) by reflexivity.
    assert (find_global_offset fns "start"%string = Some 0%nat) by reflexivity.
    eapply link_exits; eauto using prog0_correct_prelink.
  Qed.

  (* Test scaling with a large codegen. *)
  Definition repeat_add (n : nat) : function :=
    (("add" ++ String.of_nat n)%string,
      map.empty,
      (Addi x2 x0 0 : insn) :: repeat (Add x2 x2 x3 : insn) n ++ [(Ret : insn)]).
  Definition add100_fn : function := Eval vm_compute in (repeat_add 100).

  (* helper lemma *)
  Lemma mul_by_add_step x (a : word32) n :
    0 < n ->
    x = word.mul a (word.of_Z (n - 1)) ->
    word.add x a = word.mul a (word.of_Z n).
  Proof.
    intros; subst. cbv [Z.sub].
    rewrite word.ring_morph_add, word.ring_morph_opp.
    ring.
  Qed.

  Lemma add100_correct :
    forall regs wregs flags dmem cstack lstack a,
      map.get regs (gpreg x3) = Some a ->
      returns
        (fetch:=fetch_ctx [add100_fn])
        "add100"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get regs' (gpreg x2) = Some (word.mul a (word.of_Z 100))
           /\ wregs' = wregs
           /\ dmem' = dmem                
           /\ clobbers [gpreg x2] regs regs').
  Proof.
    cbv [returns]; intros.
    straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step.
    Time do 10 straightline_step. (* .57s *)

    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | ].
    { solve_map. apply (f_equal Some).
      repeat (apply mul_by_add_step; [ lia | ];
              cbn [Z.sub Z.add Z.opp Z.pos_sub Pos.pred_double]).
      lazymatch goal with |- ?x = word.mul _ (word.of_Z 0) => subst x end.
      cbv [addi_spec]. destruct_one_match; try lia; [ ].
      ring. }    
    { (* only_differ clause *)
      eapply clobbers_incl; eauto. cbv [incl In]. tauto. }
  Time Qed. (* 0.64s *)
End __.
End Test.

Require Import coqutil.Word.Naive.
Require Import coqutil.Map.SortedListWord.

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
    { abstract (cbv [flag_to_string];
                repeat destruct_one_match; apply eq_refl). }
    { abstract (eauto using String.ltb_trans). }
    { abstract (cbv [flag_to_string] in *;
                repeat destruct_one_match_hyp; try reflexivity;
                exfalso; cbv in *; try congruence). }
  Defined.

  Global Instance map : map.map flag bool :=
    SortedList.map (Build_parameters _) strict_order.
End SortedListFlags.

Global Instance mem : map.map Naive.word32 Naive.word32 := SortedListWord.map _ _.

Module ExecTest.
  Local Instance word32 : word.word 32 := Naive.word 32.
  Local Instance word256 : word.word 256 := Naive.word 256.
  (* Check that exec works *)
  Eval vm_compute in
    (exec1 (fetch:=fetch Test.prog0) start_state).
  Eval vm_compute in
    (exec (fetch:=fetch Test.prog0) start_state 100).

  (* scaling factor; create a program with ~n instructions *)
  Definition n := 10000.
  Definition add_fn : function := Eval vm_compute in (Test.repeat_add 10000).
  Definition start_fn : function :=
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
    (exec (fetch:=fetch prog) start_state (length prog)).
  (* 5s *)

End ExecTest.

(* Next: separation logic for memory (considered for regs, but doesn't make much sense given how regs are usually handled -- most useful for long values) *)
(* Next: wclobbers, fclobbers *)
(* Next: add bn.add/bn.addc and test these *)
(* Next: add mulqacc *)
(* Next: try to add more realistic error conditions for e.g. loop errors *)
(* Next: add notations back *)
(* Next: provable multiplication blocks *)
(* Next: add more insns needed for 25519 mul *)
(* Next: prove 25519 mul *)

(* TODO: think through how memory should actually work re symbols and
   labels; does everything need to be fixed? Can we add it to the
   linker? *)
(*
 option 1: have mem map be label * offset -> word32, just like jumps
   - then in proofs we'd just use the context with strings
   - linker pass would set them in some kinda order
   - unlike for jump dsts, we'd need a size (but I guess kinda like functions)
   - would need to handle both with and without initial values
   - so we'd have list function, also list (name : string, values: list word32) for data
   - and list (name : string, size : nat) for bss/scratchpad
   - would need to link straightline instructions as well as control flow for that
   - would not need seplogic in proofs


option 2: have mem map be always word32 -> word32
  - then in proos we'd deal with addresses and seplogic, and need to assume they don't overlap
  - we could plug in any separated addresses at the last stage
  - would need to pass addresses around in proofs -- but only as much as we do in code anyway
  - each proof for each function would assume seplogic
  - for functions we tie together, we'd need to include all buffers used by sub-functions
  - maybe that's OK though?

Try option 2 and see how this goes
*)
