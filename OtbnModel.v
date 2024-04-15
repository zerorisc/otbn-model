Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Section Registers.
  (* General data registers, 32 bits each. *)
  Inductive gpr : Type :=
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9
  | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19
  | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29
  | x30 | x31
  .

  (* Wide data registers, 256 bits each. *)
  Inductive wdr : Type :=
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7 | w8 | w9
  | w10 | w11 | w12 | w13 | w14 | w15 | w16 | w17 | w18 | w19
  | w20 | w21 | w22 | w23 | w24 | w25 | w26 | w27 | w28 | w29
  | w30 | w31
  .

  (* Control and status registers, 32-bits each. *)
  Inductive csr : Type :=
  | CSR_FG0
  | CSR_FG1
  | CSR_FLAGS
  | CSR_MOD0
  | CSR_MOD1
  | CSR_MOD2
  | CSR_MOD3
  | CSR_MOD4
  | CSR_MOD5
  | CSR_MOD6
  | CSR_MOD7
  | CSR_RND_PREFETCH
  | CSR_RND
  | CSR_URND
  .

  (* Wide special registers, 256 bits each. *)
  Inductive wsr : Type :=
  | MOD
  | ACC
  | RND
  | URND
  | KEY_S0_L
  | KEY_S0_H
  | KEY_S1_L
  | KEY_S1_H
  .

  (* Catchall type indicating any register. *)
  Inductive reg :=
  | gpreg : gpr -> reg
  | csreg : csr -> reg
  | wdreg : wdr -> reg
  | wsreg : wsr -> reg
  .
End Registers.

Section Flags.
  Inductive flag_group : Type :=
  | FG0
  | FG1
  .

  Inductive flag : Type :=
  | flagC : forall fg : flag_group, flag
  | flagM : forall fg : flag_group, flag
  | flagL : forall fg : flag_group, flag
  | flagZ : forall fg : flag_group, flag
  .
End Flags.

Section ISA.
  (* Indicates one lib of a wdr; used for mulqacc instructions. *)
  Inductive limb : Type :=
  | limb0 : wdr -> limb
  | limb1 : wdr -> limb
  | limb2 : wdr -> limb
  | limb3 : wdr -> limb
  .

  (* Immediate shift argument for arithmetic instructions. *)
  Inductive shift : Type :=
  | lshift : Z -> shift
  | rshift : Z -> shift
  .

  (* Straightline instructions (no control flow) *)
  Inductive Insn : Type :=
  | Mulqacc : forall (z : bool), limb -> limb -> Z -> Insn
  | Mulqacc_wo : forall (z : bool), wdr -> limb -> limb -> Z -> Insn
  | Mulqacc_so : forall (z : bool) (L : bool), wdr -> limb -> limb -> Z -> Insn
  | Addm : wdr -> wdr -> wdr -> Insn
  | Subm : wdr -> wdr -> wdr -> Insn
  | Add : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Addc : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Sub : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Subb : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Rshi : wdr -> wdr -> wdr -> Z -> Insn
  .

  (* Program graph with control flow. Block constructors are named
     after the control-flow instruction they end with. *)
  Inductive Program : Type :=
  | Ret : list Insn -> Program
  | Ecall : list Insn -> Program
  | Jump : list Insn -> Program -> Program
  | Bne : list Insn -> gpr -> gpr -> Program -> Program -> Program
  .

End ISA.

(* Notations to interpret assembly code. *)
Module Notations.
  Coercion gpreg : gpr >-> reg.
  Coercion wdreg : wdr >-> reg.
  Coercion wsreg : wsr >-> reg.
  Notation "x '.0'" := (limb0 x) (at level 0).
  Notation "x '.1'" := (limb1 x) (at level 0).
  Notation "x '.2'" := (limb2 x) (at level 0).
  Notation "x '.3'" := (limb3 x) (at level 0).
  Notation "'bn.mulqacc' a , b , imm" := (Mulqacc false a b imm) (at level 40).
  Notation "'bn.mulqacc.z' a , b , imm" := (Mulqacc true a b imm) (at level 40).
  Notation "'bn.mulqacc.wo' d , a , b , imm" := (Mulqacc_wo false d a b imm) (at level 40).
  Notation "'bn.mulqacc.wo.z' d , a , b , imm" := (Mulqacc_wo true d a b imm) (at level 40).
  Notation "'bn.mulqacc.so' d '.L' , a , b , imm" := (Mulqacc_so false true d a b imm) (at level 40).
  Notation "'bn.mulqacc.so' d '.U' , a , b , imm" := (Mulqacc_so false false d a b imm) (at level 40).
  Notation "'bn.mulqacc.so.z' d '.L' , a , b , imm" := (Mulqacc_so true true d a b imm) (at level 40).
  Notation "'bn.mulqacc.so.z' d '.U' , a , b , imm" := (Mulqacc_so true false d a b imm) (at level 40).
  Notation "'bn.addm' d , a , b " := (Addm d a b) (at level 40).
  Notation "'bn.add' d , a , b '<<' s , fg" := (Add d a b (lshift s) fg) (at level 40).
  Notation "'bn.add' d , a , b '>>' s , fg" := (Add d a b (rshift s) fg) (at level 40).

  Notation "x ;; 'ecall'" := (Ecall x) (at level 40).
  Notation "x ;; 'ret'" := (Ret x) (at level 40).
  Notation "x ;; 'jal' 'x1' , foo" := (Jump x foo) (at level 40).

  (* Test. *)
  Check (bn.add w1, w2, w3 << 0, FG0).
  Check (bn.add w1, w2, w3 >> 3, FG0).
  Check ([bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; ecall).
  Check (fun p : Program => [bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; jal x1, p).
End Notations.

(* option monad notation *)
Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.
Local Notation "a <- b ; c" := (bind b (fun a => c)) (at level 100, right associativity).
       

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

(* Executable model of OTBN. *)
Section Exec.
  (* Parameterize over randomness implementation. *)
  Context {rnd : nat -> Z}
    {rnd_range : forall n, 0 <= rnd n < 2^256}.
  (* Parameterize over the map implementation. *)
  Context {map : Type -> Type -> Type}
    {mget : forall {K V}, map K V -> K -> option V}
    {mset : forall {K V}, map K V -> K -> V -> map K V}
    {mget_mset_eq : forall K V (m : map K V) k v, mget (mset m k v) k = Some v}
    {mget_mset_neq : forall K V (m : map K V) k1 k2 v,
        k1 <> k2 -> mget (mset m k1 v) k2 = mget m k2}.
  Arguments mget {_ _}. Arguments mset {_ _}.


  

  (* State information for the processor. *)
  Record OtbnState : Type :=
    {
      (* Register file. *)
      regfile : map reg Z;
      (* Flag states. *)
      flagfile : map flag bool;
      (* Instruction memory *)
      imem : map Z Insn;
      (* Data memory *)
      dmem : map Z Z;
      (* Call stack. *)
      callstack : list Z;
      (* Loop stack. *)
      loopstack : list Z;
      (* Randomness counter (ghost state). *)
      rnd_counter : nat;
    }.

  Definition read_gpr (st : OtbnState) (r : gpr) : OtbnState * option Z :=
    match r with
    | x0 => (st, Some 0)
    | x1 =>
        
        (st', hd_error st.(callstack))
    | _ => mget st.(regfile) (gpreg r)
    end.

  Definition read_wdr (st : OtbnState) (r : wdr) : option Z := mget st.(regfile) (wdreg r).
  Print wsr.
  Definition read_wsr (st : OtbnState) (r : wsr) : option Z :=
    match r with
    | RND => 

  (* Assemble a group of flags into an integer value. *)
  Definition read_flag_group (st : OtbnState) (fg : flag_group) : option Z :=
    c <- mget st.(flagfile) (flagC fg) ;
    m <- mget st.(flagfile) (flagM fg) ;
    l <- mget st.(flagfile) (flagL fg) ;
    z <- mget st.(flagfile) (flagZ fg) ;
    Some (c |' (m << 1) |' (l << 2) |' (z << 3)).    

  Print csr.
  Definition read_csr (st : OtbnState) (r : csr) : option Z :=
    match r with
    | CSR_FG0 => read_flag_group st FG0
    | CSR_FG1 => read_flag_group st FG1
    | CSR_FLAGS =>
        (fg0 <- read_flag_group st FG0;
         fg1 <- read_flag_group st FG1;
         Some (fg0 |' (fg1 << 4)))
    | CSR_MOD0 =>
        (m <- read_wsr st.(regfile) MOD;
         
    end.
  

  (* Implements a read from the register file, handling all special registers. *)
  Definition read_reg (st : OtbnState) (r : reg) : option Z :=
    match r with
    | gpreg x0 => Some 0 (* x0 is fixed to zero *)
    | gpreg x1 =>
        (* read from x1 pops the call stack *)
        hd_error st.(callstack)
    | gpre
    | csreg r => 
        
        

  (* Executable version of the processor model (for computation). *)
  Fixpoint exec (insns : list Insn) : :=
    
  
End Exec.
