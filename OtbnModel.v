Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Coq.Strings.HexString.
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
      (* These registers are not used much in practice.
  | CSR_MOD0
  | CSR_MOD1
  | CSR_MOD2
  | CSR_MOD3
  | CSR_MOD4
  | CSR_MOD5
  | CSR_MOD6
  | CSR_MOD7
  | CSR_RND
  | CSR_URND
  | CSR_RND_PREFETCH
       *)
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

  (* TODO: maybe make this a pair *)
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

  (* Indirect register (may have increment bit set or not). *)
  Inductive ind : Type :=
  | ind_noinc : gpr -> ind
  | ind_inc : gpr -> ind
  .

  (* Straightline instructions (no control flow) *)
  Inductive sinsn : Type :=
  | Addi : gpr -> gpr -> Z -> sinsn
  | Bn_mulqacc : forall (z : bool), limb -> limb -> Z -> sinsn
  | Bn_mulqacc_wo : forall (z : bool), wdr -> limb -> limb -> Z -> sinsn
  | Bn_mulqacc_so : forall (z : bool) (L : bool), wdr -> limb -> limb -> Z -> sinsn
  | Bn_addm : wdr -> wdr -> wdr -> sinsn
  | Bn_subm : wdr -> wdr -> wdr -> sinsn
  | Bn_add : wdr -> wdr -> wdr -> shift -> flag_group -> sinsn
  | Bn_addc : wdr -> wdr -> wdr -> shift -> flag_group -> sinsn
  | Bn_sub : wdr -> wdr -> wdr -> shift -> flag_group -> sinsn
  | Bn_subb : wdr -> wdr -> wdr -> shift -> flag_group -> sinsn
  | Bn_rshi : wdr -> wdr -> wdr -> Z -> sinsn
  | Bn_movr : ind -> ind -> sinsn
  | Bn_lid : ind -> Z -> ind -> sinsn
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

(* Notations to interpret assembly code. *)
Module OtbnNotations.
  Coercion gpreg : gpr >-> reg.
  Coercion wdreg : wdr >-> reg.
  Coercion wsreg : wsr >-> reg.
  Coercion ind_noinc : gpr >-> ind.
  Coercion Straightline : sinsn >-> insn. 
  Coercion Control : cinsn >-> insn. 
  Declare Scope otbn_scope.
  Delimit Scope otbn_scope with otbn.

  Notation "x '.0'" := (limb0 x) (at level 0) : otbn_scope.
  Notation "x '.1'" := (limb1 x) (at level 0) : otbn_scope.
  Notation "x '.2'" := (limb2 x) (at level 0) : otbn_scope.
  Notation "x '.3'" := (limb3 x) (at level 0) : otbn_scope.
  Notation "a '++'" := (ind_inc a) (at level 20) : otbn_scope.
  Notation "'addi' d , a , imm" := (Addi d a imm) (at level 40) : otbn_scope. 
  Notation "'bn.mulqacc' a , b , imm" := (Bn_mulqacc false a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.z' a , b , imm" := (Bn_mulqacc true a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo' d , a , b , imm" := (Bn_mulqacc_wo false d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo.z' d , a , b , imm" := (Bn_mulqacc_wo true d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.L' , a , b , imm" := (Bn_mulqacc_so false true d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.U' , a , b , imm" := (Bn_mulqacc_so false false d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.L' , a , b , imm" := (Bn_mulqacc_so true true d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.U' , a , b , imm" := (Bn_mulqacc_so true false d a b imm) (at level 40) : otbn_scope.
  Notation "'bn.addm' d , a , b " := (Bn_addm d a b) (at level 40) : otbn_scope.
  Notation "'bn.subm' d , a , b " := (Bn_subm d a b) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b , fg" := (Bn_add d a b (lshift 0) fg) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '<<' s , fg" := (Bn_add d a b (lshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '>>' s , fg" := (Bn_add d a b (rshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b , fg" := (Bn_addc d a b (lshift 0) fg) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '<<' s , fg" := (Bn_addc d a b (lshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '>>' s , fg" := (Bn_addc d a b (rshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b , fg" := (Bn_sub d a b (lshift 0) fg) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '<<' s , fg" := (Bn_sub d a b (lshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '>>' s , fg" := (Bn_sub d a b (rshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b , fg" := (Bn_subb d a b (lshift 0) fg) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '<<' s , fg" := (Bn_subb d a b (lshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '>>' s , fg" := (Bn_subb d a b (rshift s) fg) (at level 40) : otbn_scope.
  Notation "'bn.movr' a , b" := (Bn_movr a b) (at level 40) : otbn_scope.
  Notation "'bn.lid' a , offset" := (Bn_lid a offset) (at level 10) : otbn_scope.
  Notation "'ret'" := Ret (at level 40) : otbn_scope.
  Notation "'ecall'" := Ecall (at level 40) : otbn_scope.
  Notation "'jal' a , addr" := (Jal a addr) (at level 40) : otbn_scope.
  Notation "'bne' a , b , addr" := (Bne a b addr) (at level 40) : otbn_scope.
  Notation "'beq' a , b , addr" := (Beq a b addr) (at level 40) : otbn_scope.
  Notation "'loop' a , len" := (Loop a len) (at level 40) : otbn_scope.
  Notation "'loopi' a , len" := (Loopi a len) (at level 40) : otbn_scope.

  (* Tests for instruction notations. *)
  Check (addi x3, x0, 5)%otbn.
  Check (addi x3, x0, -5)%otbn.
  Check (bn.mulqacc w2.0, w3.3, 64)%otbn.
  Check (bn.mulqacc.wo.z w4, w2.0, w3.3, 64)%otbn.
  Check (bn.mulqacc.so w4.L, w2.0, w3.3, 64)%otbn.
  Check (bn.addm w0, w1, w2)%otbn.
  Check (bn.subm w0, w1, w2)%otbn.
  Check (bn.add w0, w0, w0, FG0)%otbn.
  Check (bn.add w20, w20, w20 << 128, FG0)%otbn.
  Check (bn.add w20, w20, w20 >> 128, FG1)%otbn.
  Check (bn.addc w0, w0, w0, FG0)%otbn.
  Check (bn.addc w20, w20, w20 << 128, FG0)%otbn.
  Check (bn.addc w20, w20, w20 >> 128, FG1)%otbn.
  Check (bn.sub w0, w0, w0, FG0)%otbn.
  Check (bn.sub w20, w20, w20 << 128, FG0)%otbn.
  Check (bn.sub w20, w20, w20 >> 128, FG1)%otbn.
  Check (bn.subb w0, w0, w0, FG0)%otbn.
  Check (bn.subb w20, w20, w20 << 128, FG0)%otbn.
  Check (bn.subb w20, w20, w20 >> 128, FG1)%otbn.
  Check (bn.movr x20, x21)%otbn.
  Check (bn.movr x20++, x21)%otbn.
  Check (bn.movr x20, x21++)%otbn.
  Check (bn.lid x20, 0(x21))%otbn.
  Check (bn.lid x20, 32(x21++))%otbn.
  Check (bn.lid x20, (-32)(x21++))%otbn.
  Check (ret)%otbn.
  Check (ecall)%otbn.
  Check (bne x3, x4, 0xfde)%otbn.
  Check (beq x3, x4, 0x400)%otbn.
  Check (loop x2, 5)%otbn.
  Check (loopi 2, 5)%otbn.
End OtbnNotations.

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
Import ErrorMonadNotations.

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
  Definition wdr_eqb (r1 r2 : wdr) : bool.
  Proof. derive_eqb r1 r2. Defined.
  Definition wsr_eqb (r1 r2 : wsr) : bool.
  Proof. derive_eqb r1 r2. Defined.

  Local Ltac prove_eqb_spec r1 r2 :=
    destruct r1, r2; cbv [gpr_eqb]; constructor; congruence.
  Lemma gpr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (gpr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Lemma csr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (csr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Lemma wdr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wdr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Lemma wsr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wsr_eqb r1 r2).
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
  (* Parameterize over randomness implementation. *)
  Context {rnd : nat -> Z} {rnd_range : forall x, 0 <= rnd x < 2^256}
    {urnd : nat -> Z} {urnd_range : forall x, 0 <= urnd x < 2^256}.

  (* Parameterize over the representation of program counter. *)
  Context {addr : Type}
    {advance_pc : addr -> addr}
    {addr_eqb : addr -> addr -> bool}
    {addr_eqb_spec : forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (addr_eqb a1 a2)}.

  (* Parameterize over the map implementation. *)
  Context {map : Type -> Type -> Type}
    {mget : forall {K V}, map K V -> K -> option V}
    {mset : forall {K V}, map K V -> K -> V -> map K V}
    {mget_mset_eq : forall K V (m : map K V) k v, mget (mset m k v) k = Some v}
    {mget_mset_neq : forall K V (m : map K V) k1 k2 v,
        k1 <> k2 -> mget (mset m k1 v) k2 = mget m k2}.
  Arguments mget {_ _}. Arguments mset {_ _}.
  Notation regfile := (map reg Z) (only parsing).
  Notation flagfile := (map flag bool) (only parsing).
  Notation mem := (map Z Z) (only parsing).

  (* State information for the processor. *)
  Record OtbnState : Type :=
    {
      (* Register file. *)
      regs : regfile;
      (* Flag states. *)
      flags : flagfile;
      (* Data memory *)
      dmem : mem;
      (* Call stack: holds the IMEM address of the last calls. *)
      callstack : list addr;
      (* Loop stack: holds the IMEM start/end addresses and counter for active loops. *)
      loopstack : list (addr * addr * nat);
      (* Instruction counter. *)
      insn_counter : nat;
      (* Program counter *)
      pc : addr;
    }.

  Definition read_gpr (st : OtbnState) (r : gpr) : maybe Z :=
    match r with
    | x0 => Ok 0 (* x0 always reads as 0 *)
    | x1 =>
        (* TODO: a direct read from the call stack is possible but
           rare in practice. For now, don't model it. *)
        Err "Attempt to directly read from the call stack. This behavior is not yet modelled."
    | _ => map_err (mget st.(regs) (gpreg r)) "GPR undefined"
    end.

  Definition read_wdr (st : OtbnState) (r : wdr) : maybe Z :=
    map_err (mget st.(regs) (wdreg r)) "WDR undefined".

  Definition read_wsr (st : OtbnState) (r : wsr) : maybe Z :=
    match r with
    | RND => Ok (rnd st.(insn_counter))
    | URND => Ok (urnd st.(insn_counter))
    | _ => map_err (mget st.(regs) (wsreg r)) "WSR undefined"
    end.

  Definition read_flag (st : OtbnState) (f : flag) : maybe bool :=
    map_err (mget st.(flags) f) "Flag undefined".

  (* Assemble a group of flags into an integer value. *)
  Definition read_flag_group (st : OtbnState) (fg : flag_group) : maybe Z :=
    c <- read_flag st (flagC fg) ;
    m <- read_flag st (flagM fg) ;
    l <- read_flag st (flagL fg) ;
    z <- read_flag st (flagZ fg) ;
    Ok (c |' (m << 1) |' (l << 2) |' (z << 3)).

  Definition read_csr (st : OtbnState) (r : csr) : maybe Z :=
    match r with
    | CSR_FG0 => read_flag_group st FG0
    | CSR_FG1 => read_flag_group st FG1
    | CSR_FLAGS =>
        (fg0 <- read_flag_group st FG0;
         fg1 <- read_flag_group st FG1;
         Ok (fg0 |' (fg1 << 4)))
    end.

  (* Implements a read from the register file, handling all special registers. *)
  Definition read_reg (st : OtbnState) (r : reg) : maybe Z :=
    match r with
    | gpreg r => read_gpr st r
    | wdreg r => read_wdr st r
    | csreg r => read_csr st r
    | wsreg r => read_wsr st r
    end.

  Definition read_limb (st : OtbnState) (l : limb) : maybe Z :=
    match l with
    | limb0 r => x <- read_wdr st r; Ok (x &' Z.ones 64)
    | limb1 r => x <- read_wdr st r; Ok ((x >> 64) &' Z.ones 64)
    | limb2 r => x <- read_wdr st r; Ok ((x >> 128) &' Z.ones 64)
    | limb3 r => x <- read_wdr st r; Ok ((x >> 192) &' Z.ones 64)
  end.

  Definition inc_insn_counter (st : OtbnState) : OtbnState :=
    {| regs := st.(regs);
      flags := st.(flags);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter) + 1;
      pc := st.(pc);
    |}.

  Definition regfile_set (st : OtbnState) (r : reg) (v : Z) : OtbnState :=
    {| regs := mset st.(regs) r v;
      flags := st.(flags);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter);
      pc := st.(pc);
    |}.

  Definition flagfile_set (st : OtbnState) (f : flag) (v : bool) : OtbnState :=
    {| regs := st.(regs);
      flags := mset st.(flags) f v;
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter);
      pc := st.(pc);
    |}.
  
  Definition jump (st : OtbnState) (pc : addr) : OtbnState :=
    {| regs := st.(regs);
      flags := st.(flags);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter);
      pc := pc;
    |}.
  
  Definition callstack_pop (st : OtbnState) : maybe  OtbnState :=
    (pc <- map_err (hd_error st.(callstack)) "Call stack empty" ;
     Ok ({| regs := st.(regs);
           flags := st.(flags);
           dmem := st.(dmem);
           callstack := tl st.(callstack);
           loopstack := st.(loopstack);
           insn_counter := st.(insn_counter);
           pc := pc;
         |})).

  Definition callstack_push (st : OtbnState) (new_pc : addr) : maybe OtbnState :=
    (_ <- assertion (length st.(callstack) <? 8)%nat "Call stack full" ;
     Ok {| regs := st.(regs);
          flags := st.(flags);
          dmem := st.(dmem);
          callstack := new_pc :: st.(callstack);
          loopstack := st.(loopstack);
          insn_counter := st.(insn_counter);
          pc := st.(pc);
        |}).

  Definition loopstack_pop (st : OtbnState) : maybe ((addr * addr * nat) * OtbnState) :=
    (l <- map_err (hd_error st.(loopstack)) "Loop stack empty" ;
     Ok (l,
         {| regs := st.(regs);
           flags := st.(flags);
           dmem := st.(dmem);
           callstack := st.(callstack);
           loopstack := tl st.(loopstack);
           insn_counter := st.(insn_counter);
          pc := st.(pc);
         |})).

  Definition loopstack_push (st : OtbnState) (l : addr * addr * nat) : maybe OtbnState :=
    (_ <- assertion (length st.(loopstack) <? 8)%nat "Call stack full" ;
     Ok {| regs := st.(regs);
          flags := st.(flags);
          dmem := st.(dmem);
          callstack := st.(callstack);
          loopstack := l :: st.(loopstack);
          insn_counter := st.(insn_counter);
          pc := st.(pc);
        |}).

  Fixpoint repeat_advance_pc (pc : addr) (n : nat) : addr :=
    match n with
    | O => pc
    | S n => advance_pc (repeat_advance_pc pc n)
    end.


  (* set the M, L, and Z flags according to the destination register *)
  Definition set_mlz (st : OtbnState) (fg : flag_group) (v : Z) : OtbnState :=
    let st := flagfile_set st (flagM fg) (Z.testbit v 255) in
    let st := flagfile_set st (flagL fg) (Z.testbit v 0) in
    let st := flagfile_set st (flagZ fg) (v =? 0) in
    st.

  Definition cast32 (v : Z) : Z := v &' Z.ones 32.
  Definition cast256 (v : Z) : Z := v &' Z.ones 256.

  Definition write_gpr (st : OtbnState) (r : gpr) (v : Z) : maybe OtbnState :=
    match r with
    | x0 => Ok st
    | x1 =>
        (* TODO: this should push to the call stack, but is
           practically never used. For now, don't model this behavior
           and treat it as an error. *)
        Err "Attempt to write to call stack. This behavior is not yet modelled."
    | _ => Ok (regfile_set st (gpreg r) (cast32 v))
    end.

  Definition write_wdr (st : OtbnState) (r : wdr) (v : Z) : OtbnState :=
    regfile_set st (wdreg r) (cast256 v).
  Definition write_wsr (st : OtbnState) (r : wsr) (v : Z) : OtbnState :=
    match r with
    | RND => st (* writes to RND are ignored *)
    | URND => st (* writes to URND are ignored *)
    | _ => regfile_set st (wsreg r) (cast256 v)
    end.

  (* mulqacc shifts must be multiples of 64 *)
  Definition valid_mul_shift (s : Z) : bool :=
    ((s =? 0) || (s =? 64) || (s =? 128) || (s =? 192)).
  (* rshi shifts must be in the range [0,255] *)
  Definition valid_rshi_imm (s : Z) : bool :=
    (0 <=? s) && (s <? 256).
  (* other shift immediates must be multiples of 8 and in the range [0,248] *)
  Definition valid_arith_shift (s : shift) : bool :=
    let s := match s with
             | lshift x => x
             | rshift x => x
             end in
    ((s mod 8 =? 0) && (0 <=? s) && (s <=? 248)).
  (* immediates for addi must be in the range [-2048, 2047] *)
  Definition valid_addi_imm (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  (* offsets for loads and stores are in the range [-16384, 16352] in steps of 32 *)
  Definition valid_mem_offset (offset : Z) : bool :=
    (-16384 <=? offset) && (offset <=? 16352) && (offset mod 32 =? 0).

  (* returns whether the indirect register should be incremented *)
  Definition has_inc (x : ind) : bool :=
    match x with
    | ind_noinc r => false
    | ind_inc r => true
    end.
  (* gets the gpr corresponding to this indirect value *)
  Definition ind_to_gpr (x : ind) : gpr :=
    match x with
    | ind_noinc r => r
    | ind_inc r => r
    end.
  (* get a wdr by its index value *)
  Definition index_to_wdr (idx : Z) : maybe wdr :=
    match idx with
    | 0 => Ok w0
    | 1 => Ok w1
    | 2 => Ok w2
    | 3 => Ok w3
    | 4 => Ok w4
    | 5 => Ok w5
    | 6 => Ok w6
    | 7 => Ok w7
    | 8 => Ok w8
    | 9 => Ok w9
    | 10 => Ok w10
    | 11 => Ok w11
    | 12 => Ok w12
    | 13 => Ok w13
    | 14 => Ok w14
    | 15 => Ok w15
    | 16 => Ok w16
    | 17 => Ok w17
    | 18 => Ok w18
    | 19 => Ok w19
    | 20 => Ok w20
    | 21 => Ok w21
    | 22 => Ok w22
    | 23 => Ok w23
    | 24 => Ok w24
    | 25 => Ok w25
    | 26 => Ok w26
    | 27 => Ok w27
    | 28 => Ok w28
    | 29 => Ok w29
    | 30 => Ok w30
    | 31 => Ok w31
    | _ => Err "Invalid WDR index"
    end.
  (* gets the value from the wdr corresponding to this indirect value *)
  Definition read_ind (st : OtbnState) (x : ind) : maybe Z :=
    let r := ind_to_gpr x in
    ptr <- read_gpr st r ;
    w <- index_to_wdr (ptr &' 32) ;
    read_wdr st w.

  (* specifications for complex operations (may make proofs a little nicer) *)
  Definition mulqacc_spec (acc x y s : Z) : Z :=
    acc + (x * y) << s.
  Definition addm_spec (x y m : Z) : Z :=
    let r := x + y in
    if r >? m then r - m else r.
  Definition subm_spec (x y m : Z) : Z :=
    let r := x - y in
    if r <? 0 then r + m else r.
  Definition rshi_spec (x y imm : Z) : Z :=
    let xy := Z.lor (x << 256) y in
    xy >> imm.

  Definition exec1
    (st : OtbnState) (i : sinsn) : maybe OtbnState :=
    let st := inc_insn_counter st in
    match i with
    | Addi d x imm =>
        (_ <- assertion (valid_addi_imm imm) "Invalid immediate for addi";
         x <- read_gpr st x ;
         write_gpr st d (x + imm))
    | Bn_mulqacc z x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc";
         x <- read_limb st x ;
         y <- read_limb st y ;
         acc <- read_wsr st ACC ;
         let r := mulqacc_spec acc x y s in
         Ok (write_wsr st ACC r))
    | Bn_mulqacc_wo z d x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc.wo" ;
         x <- read_limb st x ;
         y <- read_limb st y ;
         acc <- read_wsr st ACC ;
         let r := mulqacc_spec acc x y s in
         Ok (write_wdr (write_wsr st ACC r) d r))
    | Bn_mulqacc_so z L d x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc.so" ;
         x <- read_limb st x ;
         y <- read_limb st y ;
         old <- read_wdr st d ;
         acc <- read_wsr st ACC ;
         let r := mulqacc_spec acc x y s in
         let accL := r &' (Z.ones 128) in
         let accH := r >> 128 in
         let dL := old &' (Z.ones 128) in
         let dH := old >> 128 in
         let d' := if L
                   then (accL |' (dH << 128))
                   else (dL |' (accL << 128)) in
         Ok (write_wdr (write_wsr st ACC r) d d'))
    | Bn_addm d x y =>
         (x <- read_wdr st x ;
          y <- read_wdr st y ;
          m <- read_wsr st MOD ;          
          Ok (write_wdr st d (addm_spec x y m)))
    | Bn_subm d x y =>
         (x <- read_wdr st x ;
          y <- read_wdr st y ;
          m <- read_wsr st MOD ;
          Ok (write_wdr st d (subm_spec x y m)))
    | Bn_add d x y s fg =>
        (_ <- assertion (valid_arith_shift s) "Invalid shift for bn.add" ;
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         let r := x + y in
         let st := set_mlz st fg r in
         let st := flagfile_set st (flagC fg) (2^256 <=? r) in
         Ok (write_wdr st d r))
    | Bn_addc d x y s fg =>
        (_ <- assertion (valid_arith_shift s) "Invalid shift for bn.addc" ;
         c <- read_flag st (flagC fg);
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         let r := x + y + c in
         let st := set_mlz st fg r in
         let st := flagfile_set st (flagC fg) (2^256 <=? r) in
         Ok (write_wdr st d r))
    | Bn_sub d x y s fg =>
        (_ <- assertion (valid_arith_shift s) "Invalid shift for bn.sub" ;
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         let r := x - y in
         let st := set_mlz st fg r in
         let st := flagfile_set st (flagC fg) (r <? 0) in
         Ok (write_wdr st d r))
    | Bn_subb d x y s fg =>
        (_ <- assertion (valid_arith_shift s) "Invalid shift for bn.subb" ;
         b <- read_flag st (flagC fg);
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         let r := x - y - b in
         let st := set_mlz st fg r in
         let st := flagfile_set st (flagC fg) (r <? 0) in
         Ok (write_wdr st d r))
    | Bn_rshi d x y imm =>
        (_ <- assertion (valid_rshi_imm imm) "Invalid immediate for bn.rshi" ;
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         let r := rshi_spec x y imm in
         Ok (write_wdr st d r))
    | Bn_movr x y =>
        let xinc := has_inc x in
        let yinc := has_inc y in
        let xr := ind_to_gpr x in
        let yr := ind_to_gpr y in
        (_ <- assertion (negb(xinc && yinc)) "Cannot increment both indirect registers (bn.movr)";
         src_ptr <- read_gpr st yr ;
         src <- index_to_wdr (src_ptr &' 32) ;
         addr_ptr <- read_gpr st xr ;
         addr <- index_to_wdr (addr_ptr &' 32) ;
         v <- read_wdr st src ;
         st <- (if xinc
                then write_gpr st xr (src_ptr + 1)
                else if yinc
                     then write_gpr st yr (addr_ptr + 1)
                     else Ok st) ;
         Ok (write_wdr st addr v))
    | Bn_lid x offset y =>
        let xinc := has_inc x in
        let yinc := has_inc y in
        let xr := ind_to_gpr x in
        let yr := ind_to_gpr y in
        (_ <- assertion (negb(xinc && yinc)) "Cannot increment both indirect registers (bn.lid)";
         _ <- assertion (valid_mem_offset offset) "Invalid offset for bn.lid";
         src_ptr <- read_gpr st yr ;
         src <- index_to_wdr (src_ptr &' 32) ;
         addr_ptr <- read_gpr st xr ;
         addr <- index_to_wdr (addr_ptr &' 32) ;
         v <- read_wdr st src ;
         st <- (if xinc
                then write_gpr st xr (src_ptr + 1)
                else if yinc
                     then write_gpr st yr (addr_ptr + 1)
                     else Ok st) ;
         Ok (write_wdr st addr v))
          (*
    | _ => Err "NotImplemented"
*)
    end.

  Definition exec_straightline
    (st : OtbnState) (insns : list sinsn) : maybe OtbnState :=
    fold_left (fun st i => (st <- st ;
                            st <- exec1 st i;
                            Ok (inc_insn_counter st)))
      insns (Ok st).

  Definition exec_straightline_cps {A}
    (st : OtbnState) (insns : list sinsn) (f : maybe OtbnState -> A) : A :=
    f (exec_straightline st insns).

  (* Test *)
  Import OtbnNotations.
  Goal (forall st,
           read_wdr st w2 = Ok 5 ->
           (st <- exec_straightline st
                    [(addi x2, x0, 2)%otbn;
                     (bn.add w0, w2, w2, FG0)%otbn];
            read_wdr st w0) = Ok 10).
  Proof.
    intros; cbn. destruct st.
    cbv [read_wdr inc_insn_counter regs prefix_err] in *; cbn.
    rewrite !mget_mset_neq by congruence.
    lazymatch goal with
    | H : _ = inl _ |- _ => rewrite H; cbn [bind]
    end.
    cbn [write_wdr regfile_set regs].
    rewrite ?mget_mset_neq by congruence.
    rewrite mget_mset_eq by congruence.
    reflexivity.
  Qed.

  Definition ctrl1_cps (st : OtbnState) (i : cinsn (addr:=addr))
    {A} (f : maybe OtbnState -> A) : A :=
    let st := inc_insn_counter st in
    let next_pc := advance_pc st.(pc) in
    match i with
    | Ret => f (callstack_pop st)
    | Ecall => f (Ok st)
    | Jal r jump_pc =>
        if gpr_eqb r x0
        then f (Ok (jump st jump_pc))
        else if gpr_eqb r x1
             then 
               match callstack_push st next_pc with
               | Err e => f (Err e)
               | Ok st => f (Ok (jump st jump_pc))
               end
             else f (Err "Jump-and-link for registers other than x1 or x0 is not supported.")
    | Bne r1 r2 branch_pc =>
        match read_gpr st r1, read_gpr st r2 with
        | Err e, _ => f (Err e)
        | _, Err e => f (Err e)
        | Ok v1, Ok v2 =>
            if (v1 =? v2) then f (Ok (jump st next_pc)) else f (Ok (jump st branch_pc))
        end
    | Beq r1 r2 branch_pc =>
        match read_gpr st r1, read_gpr st r2 with
        | Err e, _ => f (Err e)
        | _, Err e => f (Err e)
        | Ok v1, Ok v2 =>
            if (v1 =? v2) then f (Ok (jump st branch_pc)) else f (Ok (jump st next_pc))
        end
    | Loop r len =>
        match read_gpr st r with
        | Err e => f (Err e)
        | Ok v =>
            if (0 <=? len)%nat
            then
              if 0 <=? v
              then
                let start_addr := next_pc in
                let end_addr := repeat_advance_pc st.(pc) len in
                match loopstack_push st (start_addr, end_addr, len) with
                | Err e => f (Err e)
                | Ok st => f (Ok (jump st next_pc))
                end
              else f (Err "Loop iteration count must be > 0.")
            else f (Err "Loop instruction length must be > 0.")
        end
    | Loopi iters len =>
        if (0 <=? len)%nat
        then
          if (0 <=? iters)%nat
          then
            let start_addr := next_pc in
            let end_addr := repeat_advance_pc st.(pc) len in
            match loopstack_push st (start_addr, end_addr, iters) with
            | Err e => f (Err e)
            | Ok st => f (Ok (jump st next_pc))
            end
          else f (Err "Loop iteration count must be > 0.")
        else f (Err "Loop instruction length must be > 0.")
    end.

  Section __.
    Context (blocks : map addr (list sinsn * option (cinsn (addr:=addr)))).

    Definition exec_cps
      {A} (st : OtbnState) (f : maybe OtbnState -> A) : A :=
      match mget blocks st.(pc) with
      | None => f (Err "Block not found")
      | Some (si, ci) =>
          let end_pc := repeat_advance_pc st.(pc) (length si) in          
          exec_straightline_cps
            st si (fun st =>
                     match st with
                     | Err e => f (Err e)
                     | Ok st =>
                         match ci with
                         | None =>
                             (* Not a control-flow instruction; we
                                must have reached the end of a loop *)
                             match loopstack_pop st with
                             | Err e => f (Err e)
                             | Ok (loop_end_addr, loop_start_addr, iters, st) =>
                                 if addr_eqb end_pc loop_end_addr
                                 then
                                   match iters with
                                   | 0%nat => f (Ok (jump st (advance_pc loop_end_addr)))
                                   | S iters =>
                                       let loop_entry := (loop_end_addr, loop_start_addr, iters) in
                                       match loopstack_push st loop_entry with
                                       | Ok st => f (Ok (jump st loop_start_addr))
                                       | Err e => f (Err e)
                                       end
                                   end
                                 else f (Err "Reached loop end but loop stack did not match PC.")
                             end
                         | Some ci => ctrl1_cps (jump st end_pc) ci f
                         end
                     end)
      end.

    Definition exec (st : OtbnState) (P : OtbnState -> Prop) : Prop :=
      exec_cps st (fun x =>
                     match x with
                     | Err _ => False
                     | Ok x => P x
                     end).

    Check eventually.
    Check eventually exec.
    Check (forall (initial_state : OtbnState) (end_addr : addr),
              eventually exec (fun st =>
                                 st.(pc) = end_addr /\ read_wdr st w0 = Ok 0)
                initial_state).

    (* key thing that makes this work is that in the postcondition P
    you can specify which address you returned to *)
    (* eventually doesn't guarantee that you've returned, but you know
    because of the PC *)
    (* so for subroutines you specify in the postcondition that the PC
    is back to the caller *)

    (* one problem: you need to know all the PCs at the preprocessing
    stage to create blocks *)
    (* fine for analyzing existing programs if you can take in a
    binary, but it means that correct-by-construction is hard and also
    proofs are not reusable between different binaries *)

    (* address-independent reasoning? *)
    (* potential rep for loops: labels at start and end of loops, and
    also at not-taken branches *)
    (* then you have string -> block as context *)
    (* loop insn takes 2 labels instead of #instructions in loop *)
    (* then need a loopend instruction because you then need to know
    the labels *)
    
    (* potential solution: use strings as the index for blocks, yes,
    but don't require all strings to be actual labels *)
    (* if processing existing code, use labels for branch/jump
    destinations, but then custom identifiers for branch-not-taken and
    loop-start or loop-post destinations *)
    (* if creating new code, use whatever labels you want for these
    destinations -- they will appear in the final binary *)

    
    (* alternative: graph representation? *)
    (* duplicative representation -- same piece of code may be there
    multiple times if there is a jump/branch destination within the
    block *)
    (* for taking in a binary you can just preprocess the binary and
    maybe duplicate a bit of work *)
    (* for correct-by-construction, you build the graph explicitly and
    then assemble it -- here the duplicative rep is somewhat
    problematic. You may have the same code repeated -- maybe define
    something on the graph that assigns labels to jump points, and if
    two labels are the same then they should have the same code? As
    for jumps that go into the middle of blocks, maybe a
    postprocessing step on the assembly that sees where one block is a
    suffix of another and unifies them? or just not jump into the
    middle of blocks *)

    Print cinsn.
  
End __.
