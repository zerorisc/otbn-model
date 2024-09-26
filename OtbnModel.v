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

  (* special arguments *)
  Notation "x '.0'" := (limb0 x) (at level 0) : otbn_scope.
  Notation "x '.1'" := (limb1 x) (at level 0) : otbn_scope.
  Notation "x '.2'" := (limb2 x) (at level 0) : otbn_scope.
  Notation "x '.3'" := (limb3 x) (at level 0) : otbn_scope.
  Notation "a '++'" := (ind_inc a) (at level 20) : otbn_scope.

  (* straightline instructions *)
  Notation "'addi' d , a , imm" := (Addi d a imm : insn) (at level 40) : otbn_scope. 
  Notation "'bn.mulqacc' a , b , imm" := (Bn_mulqacc false a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.z' a , b , imm" := (Bn_mulqacc true a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo' d , a , b , imm" := (Bn_mulqacc_wo false d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo.z' d , a , b , imm" := (Bn_mulqacc_wo true d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.L' , a , b , imm" := (Bn_mulqacc_so false true d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.U' , a , b , imm" := (Bn_mulqacc_so false false d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.L' , a , b , imm" := (Bn_mulqacc_so true true d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.U' , a , b , imm" := (Bn_mulqacc_so true false d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.addm' d , a , b " := (Bn_addm d a b : insn) (at level 40) : otbn_scope.
  Notation "'bn.subm' d , a , b " := (Bn_subm d a b : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b , fg" := (Bn_add d a b (lshift 0) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '<<' s , fg" := (Bn_add d a b (lshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '>>' s , fg" := (Bn_add d a b (rshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b , fg" := (Bn_addc d a b (lshift 0) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '<<' s , fg" := (Bn_addc d a b (lshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '>>' s , fg" := (Bn_addc d a b (rshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b , fg" := (Bn_sub d a b (lshift 0) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '<<' s , fg" := (Bn_sub d a b (lshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '>>' s , fg" := (Bn_sub d a b (rshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b , fg" := (Bn_subb d a b (lshift 0) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '<<' s , fg" := (Bn_subb d a b (lshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '>>' s , fg" := (Bn_subb d a b (rshift s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.movr' a , b" := (Bn_movr a b : insn) (at level 40) : otbn_scope.

  (* Load-store offset notations require special handling to parse the
     parentheses as actual symbols. Only the most common offsets get
     notations here, unfortunately; others may need to be written
     without notation. *)
  Notation "'bn.lid' a , 0( b )" := (Bn_lid a 0 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 32( b )" := (Bn_lid a 32 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 64( b )" := (Bn_lid a 64 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 96( b )" := (Bn_lid a 96 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 128( b )" := (Bn_lid a 128 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 160( b )" := (Bn_lid a 160 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 192( b )" := (Bn_lid a 192 b : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 224( b )" := (Bn_lid a 224 b : insn) (at level 10) : otbn_scope.

  (* Control instructions. *)
  Notation "'ret'" := (Ret : insn) (at level 40) : otbn_scope.
  Notation "'ecall'" := (Ecall : insn) (at level 40) : otbn_scope.
  Notation "'jal' a , addr" := (Jal a addr : insn) (at level 40) : otbn_scope.
  Notation "'bne' a , b , addr" := (Bne a b addr : insn) (at level 40) : otbn_scope.
  Notation "'beq' a , b , addr" := (Beq a b addr : insn) (at level 40) : otbn_scope.
  Notation "'loop' a , len" := (Loop a len : insn) (at level 40) : otbn_scope.
  Notation "'loopi' a , len" := (Loopi a len : insn) (at level 40) : otbn_scope.

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
  Check (ret)%otbn.
  Check (ecall)%otbn.
  Check (bne x3, x4, 0xfde)%otbn.
  Check (beq x3, x4, 0x400)%otbn.
  Check (loop x2, 5)%otbn.
  Check (loopi 2, 5)%otbn.
End OtbnNotations.

(*
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
 *)

Section CpsMonad.
  Definition bind {A B C} (x : (A -> C) -> C) (f : A -> (B -> C) -> C) : (B -> C) -> C :=
    fun P => x (fun a => f a P).
  Definition ret {A B} (a : A) (P : A -> B) : B := P a.
End CpsMonad.
Module CpsMonadNotations.
  Notation "a <- b ; c" := (bind b (fun a => c)) (at level 100, right associativity).
  Notation Ok := inl (only parsing).
  Notation "'Err' x" := (inr x%string) (at level 20, only parsing).
End CpsMonadNotations.
Import CpsMonadNotations.

Module CpsMonadTest.
  Local Definition add_cps (a b : nat) (P : nat -> Prop) : Prop :=
    let ab := (a + b)%nat in
    P ab.

  Eval cbv beta iota delta [add_cps] in
    (fun a b c d e =>
       add_cps a b
         (fun w => add_cps w c
                     (fun x => add_cps x d
                                 (fun y => add_cps y e
                                             (fun z => z = y))))).
  Eval cbv beta iota delta [add_cps] in
    (fun a b c d e =>
       (w <- add_cps a b ;
        x <- add_cps w c ;
        y <- add_cps x d ;
        z <- add_cps y e ;
        ret (z = y))).

  Local Fixpoint mul_cps (a b : nat) : (nat -> Prop) -> Prop :=
    match b with
    | O => ret 0%nat
    | S b =>
        x <- mul_cps a b ;
        add_cps x a
    end.

  Goal (forall a, mul_cps a 5 (fun x => x = 5 * a))%nat.
  Proof.
    intros. cbv beta iota delta [mul_cps add_cps bind ret].
    cbn. lia.
  Qed.
End CpsMonadTest.


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
  (* Parameterize over the representation of code locations. *)
  Context {addr : Type}
    {error_addr : addr}
    {advance_pc : addr -> addr}
    {addr_eqb : addr -> addr -> bool}
    {addr_eqb_spec : forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (addr_eqb a1 a2)}.

  (* error values for cases that should be unreachable *)
  Context {error_Z : Z} {error_bool : bool}.

  (* Parameterize over the map implementation. *)
  Context {regfile : map.map reg Z}
    {flagfile : map.map flag bool}
    {mem : map.map Z Z}
    {blockmap : map.map addr (list sinsn * option (cinsn (addr:=addr)))}.

  (* Really, I want to talk about terminal states -- either a return
     from the subroutine, the end of the program, or an error.

     straightline needs/edits only regs, flags, dmem --> but can error
     control needs/edits callstack, loopstack, pc, needs regs --> can also error 

     need to process through, come out with a Prop in the end via cps style passing
     the prop gives you rnd reasoning much easier
   *)
  (* mulqacc shifts must be positive multiples of 64 *)
  Definition is_valid_mul_shift (s : Z) : Prop :=
    s = 0 \/ s = 64 \/ s = 128 \/ s = 192.
  (* rshi shifts must be in the range [0,255] *)
  Definition is_valid_rshi_imm (s : Z) : Prop := 0 <= s < 256.
  (* other shift immediates must be multiples of 8 and in the range [0,248] *)
  Definition is_valid_arith_shift (s : shift) : Prop :=
    let s := match s with
             | lshift x => x
             | rshift x => x
             end in
    (s mod 8 = 0) /\ 0 <= s < 256.
  (* immediates for addi must be in the range [-2048, 2047] *)
  Definition is_valid_addi_imm (imm : Z) : Prop :=
    -2048 <= imm <= 2047.
  (* offsets for loads and stores are in the range [-16384, 16352] in steps of 32 *)
  Definition is_valid_mem_offset (offset : Z) : Prop :=
    -16384 <= offset <= 16352.

  (*
  (* mulqacc shifts must be positive multiples of 64 *)
  Definition to_valid_mul_shift (s : Z) : Z :=
    Z.shiftl (Z.land (Z.shiftr (Z.abs s) 6) 3) 6.
  (* rshi shifts must be in the range [0,255] *)
  Definition to_valid_rshi_imm (s : Z) : Z := Z.land (Z.abs s) 255.
  (* other shift immediates must be multiples of 8 and in the range [0,248] *)
  Definition to_valid_arith_shift (s : shift) : Z :=
    let s := match s with
             | lshift x => x
             | rshift x => x
             end in
    Z.shiftl (Z.land (Z.shiftr (Z.abs s) 3) 31) 3.
  (* immediates for addi must be in the range [-2048, 2047] *)
  (* TODO: this implementation cuts off the very lowest value, -2048 *)
  Definition to_valid_addi_imm (imm : Z) : Z :=
    if 0 <=? imm
    then Z.land imm 2047
    else - (Z.land (-imm) 2047).
  (* offsets for loads and stores are in the range [-16384, 16352] in steps of 32 *)
  (* TODO: this implementation cuts off the very lowest value, -16384 *)
  Definition to_valid_mem_offset (offset : Z) : Z :=
    if 0 <=? offset
    then Z.shiftl (Z.land (Z.shiftr offset 5) 511) 5
    else - Z.shiftl (Z.land (Z.shiftr (- offset) 5) 511) 5.
   *)
  Definition read_gpr (regs : regfile) (r : gpr) : option Z :=
    match r with
    | x0 => Some 0 (* x0 always reads as 0 *)
    | x1 =>
        (* TODO: call stack reads are rare in practice; for now, don't model *)
        None
    | _ => map.get regs (gpreg r)
    end.

  Definition read_wdr (regs : regfile) (r : wdr) : option Z :=
    map.get regs (wdreg r).

  Definition read_wsr (regs : regfile) (r : wsr) (P : Z -> Prop) : Prop :=
    match r with
    | RND => forall r, P r
    | URND => forall u, P u
    | _ => exists v, map.get regs (wsreg r) = Some v /\ P v
    end.

  Definition read_flag (flags : flagfile) (f : flag) : option bool :=
    map.get flags f.

  (* Assemble a group of flags into an integer value. *)
  Definition read_flag_group (flags : flagfile) (fg : flag_group) (P : Z -> Prop) : Prop :=
    exists c m l z,
      read_flag flags (flagC fg) = Some c
      /\ read_flag flags (flagM fg) = Some m
      /\ read_flag flags (flagL fg) = Some l
      /\ read_flag flags (flagZ fg) = Some z
      /\ P (c |' (m << 1) |' (l << 2) |' (z << 3)).

  Definition read_csr (flags : flagfile) (r : csr) (P : Z -> Prop) : Prop :=
    match r with
    | CSR_FG0 => read_flag_group flags FG0 P
    | CSR_FG1 => read_flag_group flags FG1 P
    | CSR_FLAGS =>
        read_flag_group flags FG0
          (fun fg0 => read_flag_group flags FG1
                        (fun fg1 => P (fg0 |' (fg1 << 4))))
    end.

  Definition wdr_for_limb (l : limb) : wdr :=
    match l with
    | limb0 r => r
    | limb1 r => r
    | limb2 r => r
    | limb3 r => r
    end.
  Definition get_limb (l : limb) (v : Z) :=
    match l with
    | limb0 r => (v          &' Z.ones 64)
    | limb1 r => ((v >> 64 ) &' Z.ones 64)
    | limb2 r => ((v >> 128) &' Z.ones 64)
    | limb3 r => ((v >> 192) &' Z.ones 64)
    end.

  Definition cast32 (v : Z) : Z := v &' Z.ones 32.
  Definition cast256 (v : Z) : Z := v &' Z.ones 256.

  Definition write_gpr (regs : regfile) (r : gpr) (v : Z) : (regfile -> Prop) -> Prop :=
    match r with
    | x0 => ret regs
    | x1 =>
        (* TODO: this should push to the call stack, but is
           practically never used. For now, don't model this behavior
           and treat it as an error. *)
        fun _ => False
    | _ => ret (map.put regs (gpreg r) (cast32 v))
    end.

  Definition write_wdr (regs : regfile) (r : wdr) (v : Z) : regfile :=
    map.put regs (wdreg r) (cast256 v).
  Definition write_wsr (regs : regfile) (r : wsr) (v : Z) : regfile :=
    match r with
    | RND => regs (* writes to RND are ignored *)
    | URND => regs (* writes to URND are ignored *)
    | _ => map.put regs (wsreg r) (cast256 v)
    end.

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

  Definition run1
    (regs : regfile) (flags : flagfile) (dmem : mem)
    (i : sinsn) (post : regfile -> flagfile -> mem -> Prop) : Prop :=
    match i with
    | Addi d x imm =>
        is_valid_addi_imm imm /\
          (exists v,
              read_gpr regs x = Some v
              /\ write_gpr regs d (v + imm)
                   (fun regs => post regs flags dmem))
    | Bn_mulqacc z x y s =>
        is_valid_mul_shift s
        /\ let regs := if z then write_wsr regs ACC 0 else regs in
           (exists vx vy,
               read_wdr regs (wdr_for_limb x) = Some vx
               /\ read_wdr regs (wdr_for_limb y) = Some vy
               /\ read_wsr regs ACC
                    (fun acc =>
                       let x := get_limb x vx in
                       let y := get_limb y vy in
                       let r := mulqacc_spec acc x y s in
                       let regs := write_wsr regs ACC r in
                       post regs flags dmem))
    | Bn_mulqacc_wo z d x y s =>
        is_valid_mul_shift s
        /\ let regs := if z then write_wsr regs ACC 0 else regs in
           (exists vx vy,
               read_wdr regs (wdr_for_limb x) = Some vx
               /\ read_wdr regs (wdr_for_limb y) = Some vy
               /\ read_wsr regs ACC
                    (fun acc =>
                       let x := get_limb x vx in
                       let y := get_limb y vy in
                       let r := mulqacc_spec acc x y s in
                       let regs := write_wsr regs ACC r in
                       let regs := write_wdr regs d r in
                       post regs flags dmem))
    | _ => False
    end.

  Goal (map.ok regfile ->
        run1
           (map.put map.empty (gpreg x2) 5)
           map.empty map.empty
           (Addi x3 x2 4)
           (fun r f d =>
              run1 r f d
                (Addi x4 x3 (-4))
                (fun r f d => read_gpr r x4 = Some 5))).
  Proof.
    cbv [run1].
    intros.
    ssplit; [ cbv [is_valid_addi_imm]; lia | ].
    eexists; ssplit; [ | ].
    { cbv [read_gpr].
      repeat progress (rewrite ?map.get_put_diff, ?map.get_put_same by congruence).
      reflexivity. }
    cbv [write_gpr ret].
    ssplit; [ cbv [is_valid_addi_imm]; lia | ].
    eexists; ssplit; [ | ].
    { cbv [read_gpr].
      repeat progress (rewrite ?map.get_put_diff, ?map.get_put_same by congruence).
      reflexivity. }
    cbv [read_gpr].
    repeat progress (rewrite ?map.get_put_diff, ?map.get_put_same by congruence).
    reflexivity.
  Qed.
    
  
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

  Inductive OtbnState : Type :=
  | OtbnBusy :
    forall (regs : regfile) (flags : flagfile) (dmem : mem)
           (callstack : list addr) (loopstack : list (addr * addr * nat)),
      OtbnState
  | OtbnErr : forall (err_code : Z) (msg : string), OtbnState
  | OtbnDone : forall (dmem : mem), OtbnState
  | OtbnReturn :
    forall (regs : regfile) (flags : flagfile) (dmem : mem),
      OtbnState
  .

  Definition exec (st : OtbnState) (P : OtbnState -> Prop) : Prop :=
    exec_cps st (fun x =>
                   match x with
                   | Err _ => False
                   | Ok x => P x
                   end).

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
      (* Program counter. *)
      pc : addr;
      (* Errors. *)
      errs : 
    }.

  (* Called when OTBN encounters an error or ecall. *)
  Definition wipe (st : OtbnState) : OtbnState :=
    {| regs := map.empty;
      flags := map.empty;
      dmem := st.(dmem);
      callstack := [];
      loopstack := [];
      insn_counter := st.(insn_counter);
      pc := st.(pc);
    |}.

  Definition reg_get (st : OtbnState) (r : reg) : Z :=
    match map.get st.(regs) r with
    | Some v => v
    | None => error_Z
    end.

  Definition read_gpr (st : OtbnState) (r : gpr) : Z :=
    match r with
    | x0 => 0 (* x0 always reads as 0 *)
    | x1 =>
        (* TODO: call stack reads are rare in practice; for now, don't model *)
        error_Z
    | _ => reg_get st (gpreg r)
    end.

  Definition read_wdr (st : OtbnState) (r : wdr) : Z := reg_get st (wdreg r).

  Definition read_wsr (st : OtbnState) (r : wsr) : Z :=
    match r with
    | RND => rnd st.(insn_counter)
    | URND => urnd st.(insn_counter)
    | _ => reg_get st (wsreg r)
    end.

  Definition read_flag (st : OtbnState) (f : flag) : bool :=
    match map.get st.(flags) f with
    | Some v => v
    | None => error_bool
    end.

  (* Assemble a group of flags into an integer value. *)
  Definition read_flag_group (st : OtbnState) (fg : flag_group) : Z :=
    let c := read_flag st (flagC fg) in
    let m := read_flag st (flagM fg) in
    let l := read_flag st (flagL fg) in
    let z := read_flag st (flagZ fg) in
    c |' (m << 1) |' (l << 2) |' (z << 3).

  Definition read_csr (st : OtbnState) (r : csr) : Z :=
    match r with
    | CSR_FG0 => read_flag_group st FG0
    | CSR_FG1 => read_flag_group st FG1
    | CSR_FLAGS =>
        let fg0 := read_flag_group st FG0 in
        let fg1 := read_flag_group st FG1 in
        fg0 |' (fg1 << 4)
    end.

  (* Implements a read from the register file, handling all special registers. *)
  Definition read_reg (st : OtbnState) (r : reg) : Z :=
    match r with
    | gpreg r => read_gpr st r
    | wdreg r => read_wdr st r
    | csreg r => read_csr st r
    | wsreg r => read_wsr st r
    end.

  Definition read_limb (st : OtbnState) (l : limb) : Z :=
    match l with
    | limb0 r => (read_wdr st r) &' Z.ones 64
    | limb1 r => ((read_wdr st r) >> 64) &' Z.ones 64
    | limb2 r => ((read_wdr st r) >> 128) &' Z.ones 64
    | limb3 r => ((read_wdr st r) >> 192) &' Z.ones 64
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
    {| regs := map.put st.(regs) r v;
      flags := st.(flags);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter);
      pc := st.(pc);
    |}.

  Definition flagfile_set (st : OtbnState) (f : flag) (v : bool) : OtbnState :=
    {| regs := st.(regs);
      flags := map.put st.(flags) f v;
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
  
  Definition callstack_pop (st : OtbnState) : OtbnState :=
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
  Goal (forall st,
           map.ok regfile ->
           read_wdr st w2 = Ok 5 ->
           (st <- exec_straightline st
                    ([Addi x2 x0 2;
                      Bn_add w0 w2 w2 (lshift 0) FG0]);
            read_wdr st w0) = Ok 10).
  Proof.
    intros; cbn. destruct st.
    cbv [read_wdr inc_insn_counter regs prefix_err] in *; cbn.
    rewrite !map.get_put_diff by congruence.
    lazymatch goal with
    | H : _ = inl _ |- _ => rewrite H; cbn [bind]
    end.
    cbn [write_wdr regfile_set regs].
    rewrite ?map.get_put_diff by congruence.
    rewrite ?map.get_put_same by congruence.
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
    Context (blocks : map.rep (map:=blockmap)).

    Definition exec_cps
      {A} (st : OtbnState) (f : maybe OtbnState -> A) : A :=
      match map.get blocks st.(pc) with
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

    (* question: how do you create blocks? *)
    (* can use Z when processing binaries, since you know PC ahead of time *)
    (* can use string + offset for correct-by-construction *)

    (* need a definition that parses list of insns into blocks *)
    (* need a way to construct subroutines as blocks *)
    (* keep in mind that PCs are relative in binaries *)


  End __.

  Section TestProof.
    Context {start_addr pow32_addr : addr}
      {addrs_disjoint :
        NoDup [start_addr; advance_pc (start_addr); advance_pc (advance_pc (start_addr));
               pow32_addr; advance_pc (pow32_addr); advance_pc (advance_pc (pow32_addr))]}.
    Import OtbnNotations.

    Definition pow32_program : list (insn (addr:=Z)) :=
      [
        (* start: *)
        jal x1, 8
        ; ecall
        (* pow32: *)
        ; loopi 5, 1
        ; bn.add w2, w2, w2, FG0
        ; ret
      ]%otbn.

    Definition pow32_blocks : map.rep (map:=blockmap) :=
      let blocks := map.empty in
      let pc := pow32_addr in
      let blocks := map.put blocks pc ([], Some (Loopi 5 1)) in
      let pc := advance_pc pc in
      let blocks := map.put blocks pc ([Bn_add w2 w2 w2 (lshift 0) FG0], None) in
      let pc := advance_pc pc in
      let blocks := map.put blocks pc ([], Some Ret) in
      blocks.
    Definition start_blocks : map.rep (map:=blockmap) :=
      let blocks := map.empty in
      let pc := start_addr in 
      let blocks := map.put blocks pc ([], Some (Jal x1 pow32_addr)) in
      let pc := advance_pc start_addr in 
      let blocks := map.put blocks pc ([], Some Ecall) in
      blocks.

    Lemma pow32_disjoint :
      pow32_addr <> advance_pc (pow32_addr)
      /\ pow32_addr <> advance_pc (advance_pc (pow32_addr))
      /\ advance_pc (pow32_addr) <> advance_pc (advance_pc (pow32_addr)).
    Admitted.

    Ltac mapsimpl :=
      rewrite ?map.get_put_diff by congruence;
      multimatch goal with
      | |- context [map.get (map.put ?m ?k1 ?v) ?k2] =>
          replace (map.put m k1 v) with (map.put m k2 v) by congruence;
          rewrite (map.get_put_same m k2 v)
      end.

    Lemma exec_straightline_cps_empty (st : OtbnState) {A} (f : _ -> A) :
      exec_straightline_cps st [] f = f (Ok st).
    Proof. reflexivity. Qed.

    Lemma repeat_advance_pc_0 (pc : addr) : repeat_advance_pc pc 0 = pc.
    Proof. reflexivity. Qed.

    Lemma jump_noop (st : OtbnState) (dst : addr) :
      st.(pc) = dst -> jump st dst = st.
    Proof. intros; subst; destruct st; reflexivity. Qed.

    Lemma ctrl1_loopi (st : OtbnState) iters looplen :
      (length st.(loopstack) < 8)%nat ->
      ctrl1_cps st (Loopi iters looplen)
        (fun st' => match st' with
                    | inl st' =>
                        (st'.(regs) = st.(regs)
                         /\ st'.(flags) = st.(flags)
                         /\ st'.(dmem) = st.(dmem)
                         /\ st'.(callstack) = st.(callstack)
                         /\ st'.(loopstack) =
                              (advance_pc st.(pc), repeat_advance_pc st.(pc) looplen, iters)
                                :: st.(loopstack)
                         /\ st'.(insn_counter) = (st.(insn_counter) + 1)%nat
                         /\ st'.(pc) = advance_pc (st.(pc)))
                    | inr _ => False
                    end).
    Proof.
      intros. cbv [ctrl1_cps inc_insn_counter jump loopstack_push assertion bind].
      cbn [pc insn_counter loopstack callstack regs flags dmem].
      repeat lazymatch goal with
             | |- context [(?x <=? ?y)%nat] =>
                 destruct (Nat.leb_spec x y); try lia
             | |- context [(?x <? ?y)%nat] =>
                 destruct (Nat.ltb_spec x y); try lia
             end.
      cbn [pc insn_counter loopstack callstack regs flags dmem].
      ssplit; reflexivity.
    Qed.

    Lemma exec_straightline_cps_weaken (st : OtbnState) (insns : list sinsn) (P : _ -> Prop) :
      forall (Q : _ -> Prop),
        exec_straightline_cps st insns Q ->
        (forall st', Q st' -> P st') ->
        exec_straightline_cps st insns P.
    Proof. cbv [exec_straightline_cps exec_straightline]. intros; eauto. Qed.

    Lemma pow32_correct (st : OtbnState) :
      map.ok blockmap ->
      (0 < length st.(callstack))%nat ->
      (length st.(loopstack) < 8)%nat ->
      st.(pc) = pow32_addr ->
      forall v,
        map.get st.(regs) w2 = Some v ->
        eventually (exec pow32_blocks)
          (fun st' =>
             st'.(pc) = hd pow32_addr st.(callstack)
             /\ st'.(dmem) = st.(dmem)
             /\ st'.(loopstack) = st.(loopstack)
             /\ st'.(callstack) = tl st.(callstack)
             /\ st'.(regs) = map.put st.(regs) w2 (v ^ 32)
             /\ st'.(insn_counter) = (st.(insn_counter) + 7)%nat)
        st.
    Proof.
      intros.
      pose proof pow32_disjoint.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             end.
      
      eapply eventually_step.
      { cbv [exec exec_cps pow32_blocks]. mapsimpl.
        rewrite exec_straightline_cps_empty.
        rewrite repeat_advance_pc_0.
        rewrite jump_noop by congruence.
        apply ctrl1_loopi. lia. }


      cbv beta; intros.
      repeat lazymatch goal with
             | H : _ /\ _ |- _ => destruct H
             end.
      eapply eventually_step.
      { cbv [exec exec_cps pow32_blocks]. mapsimpl.
        cbv [exec_straightline_cps exec_straightline]. cbn [fold_left].
        eapply exec_straightline_cps_weaken.
        
        
        (* need weakening lemma for exec_straightline_cps, then lemma for Bn_add *)
        (* TODO: maybe separate OTBN control state from regs/flags? *)
        (* TODO: maybe eliminate insn counter? *)
        (* TODO: eliminate maybes, use err bits -- for imms and shifts do a mod or drop bits *)
        
      

    Qed.
End TestProof.

  Check exec.
  Fixpoint to_blocks (insns : list (insn (addr:=Z))) : :=
    


  
End Exec.
End __.
