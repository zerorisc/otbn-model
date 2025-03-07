Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.


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
(* XXX: Omit these registers for now, they are ~never used in practice.
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
| flagC : bool -> flag
.

Definition flag_group : Type := bool.
Definition FG0 : flag_group := false.
Definition FG1 : flag_group := true.

(* A GPR that may or may not be incremented by the instruction. *)
Inductive gpr_inc : Type :=
| gpr_inc_false : gpr -> gpr_inc
| gpr_inc_true : gpr -> gpr_inc
.

Definition limb : Type := (wdr * Z).

(* Straightline instructions (no control flow) *)
Inductive sinsn : Type :=
| Addi : gpr -> gpr -> Z -> sinsn
| Lui : gpr -> Z -> sinsn
| Add : gpr -> gpr -> gpr -> sinsn
| Sub : gpr -> gpr -> gpr -> sinsn
| Sll : gpr -> gpr -> gpr -> sinsn
| Slli : gpr -> gpr -> Z -> sinsn
| Srl : gpr -> gpr -> gpr -> sinsn
| Srli : gpr -> gpr -> Z -> sinsn
| Sra : gpr -> gpr -> gpr -> sinsn
| Srai : gpr -> gpr -> Z -> sinsn
| And : gpr -> gpr -> gpr -> sinsn
| Andi : gpr -> gpr -> Z -> sinsn
| Or : gpr -> gpr -> gpr -> sinsn
| Ori : gpr -> gpr -> Z -> sinsn
| Xor : gpr -> gpr -> gpr -> sinsn
| Xori : gpr -> gpr -> Z -> sinsn
| Lw : gpr -> gpr -> Z -> sinsn
| Sw : gpr -> gpr -> Z -> sinsn
| Csrrs : gpr -> csr -> gpr -> sinsn
| Csrrw : gpr -> csr -> gpr -> sinsn
| Bn_and : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_xor : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_or : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_not : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_rshi : wdr -> wdr -> wdr -> Z -> sinsn
| Bn_sel : wdr -> wdr -> wdr -> flag -> sinsn
| Bn_cmp : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_cmpb : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_add : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_addc : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_addi : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_sub : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_subb : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_subi : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_addm : wdr -> wdr -> wdr -> sinsn
| Bn_subm : wdr -> wdr -> wdr -> sinsn
| Bn_mulqacc : bool -> limb -> limb -> Z -> sinsn
| Bn_mulqacc_wo : bool -> wdr -> limb -> limb -> Z -> sinsn
| Bn_mulqacc_so : bool -> wdr -> bool -> limb -> limb -> Z -> sinsn
| Bn_mov : wdr -> wdr -> sinsn
| Bn_movr : gpr_inc -> gpr_inc -> sinsn
| Bn_lid : gpr_inc -> gpr_inc -> Z -> sinsn
| Bn_sid : gpr_inc -> gpr_inc -> Z -> sinsn
| Bn_wsrr : wdr -> wsr -> sinsn
| Bn_wsrw : wsr -> wdr -> sinsn
.

(* Control-flow instructions *)
Inductive cinsn {label : Type} : Type :=
(* XXX: ret is a special case of JALR, but only RET is used in
   practice *)
| Ret : cinsn
| Ecall : cinsn
| Unimp : cinsn (* causes an error *)
| Jal : gpr -> label -> cinsn
| Bne : gpr -> gpr -> label -> cinsn
| Beq : gpr -> gpr -> label -> cinsn
| Loop : gpr -> cinsn
| Loopi : nat -> cinsn
(* Note: loops here use an end instruction instead of an iteration
   count to make codegen and processing easier (can be converted) *)
| LoopEnd : cinsn
.

Inductive insn {label : Type} : Type :=
| Straightline : sinsn -> insn
| Control : cinsn (label:=label) -> insn
.

Module Coercions.
  Coercion gpreg : gpr >-> reg.
  Coercion csreg : csr >-> reg.
  Coercion wdreg : wdr >-> wreg.
  Coercion wsreg : wsr >-> wreg.
  Coercion gpr_inc_false : gpr >-> gpr_inc.
  Coercion Straightline : sinsn >-> insn.
  Coercion Control : cinsn >-> insn.
End Coercions.

Import ListNotations.
(* Notations to interpret assembly code. *)
Module Notations.
  Import Coercions.
  Declare Scope otbn_scope.
  Delimit Scope otbn_scope with otbn.
  Bind Scope otbn_scope with insn.

  (* notations for certain special-form arguments *)
  Notation "x .0" := ((x, 0%Z) : limb) (at level 20) : otbn_scope.
  Notation "x .1" := ((x, 1%Z) : limb) (at level 20) : otbn_scope.
  Notation "x .2" := ((x, 2%Z) : limb) (at level 20) : otbn_scope.
  Notation "x .3" := ((x, 3%Z) : limb) (at level 20) : otbn_scope.
  Notation "x ++" := (gpr_inc_true x) (at level 20) : otbn_scope.
  Notation "x .M" := (flagM x : flag) (at level 20) : otbn_scope.
  Notation "x .Z" := (flagZ x : flag) (at level 20) : otbn_scope.
  Notation "x .C" := (flagC x : flag) (at level 20) : otbn_scope.
  (* .L conflicts with bn.mulqacc.so so it's special *)
  Notation "FG0.L" := (flagL FG0 : flag) (at level 20) : otbn_scope.
  Notation "FG1.L" := (flagL FG1 : flag) (at level 20) : otbn_scope.

  (* basic 32-bit straightline instructions (not load/store) *)
  Notation "'addi' d , a , imm" := (Addi d a imm : insn) (at level 40) : otbn_scope. 
  Notation "'lui' a , imm" := (Lui a imm : insn) (at level 40) : otbn_scope.
  Notation "'add' d , a , b" := (Add d a b : insn) (at level 40) : otbn_scope.
  Notation "'sub' d , a , b" := (Sub d a b : insn) (at level 40) : otbn_scope.
  Notation "'sll' d , a , b" := (Sll d a b : insn) (at level 40) : otbn_scope.
  Notation "'slli' d , a , b" := (Slli d a b : insn) (at level 40) : otbn_scope.
  Notation "'srl' d , a , b" := (Srl d a b : insn) (at level 40) : otbn_scope.
  Notation "'srli' d , a , b" := (Srli d a b : insn) (at level 40) : otbn_scope.
  Notation "'sra' d , a , b" := (Sra d a b : insn) (at level 40) : otbn_scope.
  Notation "'srai' d , a , b" := (Srai d a b : insn) (at level 40) : otbn_scope.
  Notation "'and' d , a , b" := (And d a b : insn) (at level 40) : otbn_scope.
  Notation "'andi' d , a , b" := (Andi d a b : insn) (at level 40) : otbn_scope.
  Notation "'or' d , a , b" := (Or d a b : insn) (at level 40) : otbn_scope.
  Notation "'ori' d , a , b" := (Ori d a b : insn) (at level 40) : otbn_scope.
  Notation "'xor' d , a , b" := (Xor d a b : insn) (at level 40) : otbn_scope.
  Notation "'xori' d , a , b" := (Xori d a b : insn) (at level 40) : otbn_scope.
  Notation "'csrrs' d , a , b" := (Csrrs d a b : insn) (at level 40) : otbn_scope.
  Notation "'csrrw' d , a , b" := (Csrrw d a b : insn) (at level 40) : otbn_scope.

  (* wide register instructions with no special requirements *)
  Notation "'bn.addm' d , a , b " := (Bn_addm d a b : insn) (at level 40) : otbn_scope.
  Notation "'bn.subm' d , a , b " := (Bn_subm d a b : insn) (at level 40) : otbn_scope.
  Notation "'bn.movr' d , a" := (Bn_movr d a : insn) (at level 40) : otbn_scope.
  Notation "'bn.mov' d , a" := (Bn_mov d a : insn) (at level 40) : otbn_scope.
  Notation "'bn.wsrr' d , a" := (Bn_wsrr d a : insn) (at level 40) : otbn_scope.
  Notation "'bn.wsrw' d , a" := (Bn_wsrw d a : insn) (at level 40) : otbn_scope.
  Notation "'bn.sel' d , a , b , f" := (Bn_sel d a b f : insn) (at level 40) : otbn_scope.
  Notation "'bn.rshi' d , a , b >> s" := (Bn_rshi d a b s : insn) (at level 40) : otbn_scope.

  (* wide register arithmetic instructions with flag groups *)
  Notation "'bn.addi' d , a , b" := (Bn_addi d a b FG0 : insn) (at level 40) : otbn_scope.
  Notation "'bn.addi' d , a , b , fg" := (Bn_addi d a b fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subi' d , a , b" := (Bn_subi d a b FG0 : insn) (at level 40) : otbn_scope.
  Notation "'bn.subi' d , a , b , fg" := (Bn_subi d a b fg : insn) (at level 40) : otbn_scope.

  (* wide register arithmetic instructions with shifts (and flag groups) *)
  Notation "'bn.and' d , a , b , fg" := (Bn_and d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.and' d , a , b '<<' s , fg" := (Bn_and d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.and' d , a , b '>>' s , fg" := (Bn_and d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.xor' d , a , b , fg" := (Bn_xor d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.xor' d , a , b '<<' s , fg" := (Bn_xor d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.xor' d , a , b '>>' s , fg" := (Bn_xor d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.or' d , a , b , fg" := (Bn_or d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.or' d , a , b '<<' s , fg" := (Bn_or d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.or' d , a , b '>>' s , fg" := (Bn_or d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.not' d , a , fg" := (Bn_not d a 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.not' d , a '<<' s , fg" := (Bn_not d a s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.not' d , a '>>' s , fg" := (Bn_not d a (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b , fg" := (Bn_add d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '<<' s , fg" := (Bn_add d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.add' d , a , b '>>' s , fg" := (Bn_add d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b , fg" := (Bn_addc d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '<<' s , fg" := (Bn_addc d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.addc' d , a , b '>>' s , fg" := (Bn_addc d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b , fg" := (Bn_sub d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '<<' s , fg" := (Bn_sub d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.sub' d , a , b '>>' s , fg" := (Bn_sub d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b , fg" := (Bn_subb d a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '<<' s , fg" := (Bn_subb d a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.subb' d , a , b '>>' s , fg" := (Bn_subb d a b (-s) fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmp' a , b , fg" := (Bn_cmp a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmp' a , b '<<' s , fg" := (Bn_cmp a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmp' a , b '>>' s , fg" := (Bn_cmp a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmpb' a , b , fg" := (Bn_cmpb a b 0 fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmpb' a , b '<<' s , fg" := (Bn_cmpb a b s fg : insn) (at level 40) : otbn_scope.
  Notation "'bn.cmpb' a , b '>>' s , fg" := (Bn_cmpb a b (-s) fg : insn) (at level 40) : otbn_scope.

  (* bn.mulqacc needs multiple declarations. *)
  Notation "'bn.mulqacc' a , b , imm" := (Bn_mulqacc false a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.z' a , b , imm" := (Bn_mulqacc true a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo' d , a , b , imm" := (Bn_mulqacc_wo false d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.wo.z' d , a , b , imm" := (Bn_mulqacc_wo true d a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.L' , a , b , imm" := (Bn_mulqacc_so false d false a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so' d '.U' , a , b , imm" := (Bn_mulqacc_so false d true a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.L' , a , b , imm" := (Bn_mulqacc_so true d false a b imm : insn) (at level 40) : otbn_scope.
  Notation "'bn.mulqacc.so.z' d '.U' , a , b , imm" := (Bn_mulqacc_so true d true a b imm : insn) (at level 40) : otbn_scope.

  (* Load-store offset notations require special handling to parse the
     parentheses as actual symbols. Only the most common offsets get
     notations here, unfortunately; others may need to be written
     without notation. *)
  Notation "'lw' a , 0( b )" := (Lw a b 0 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 4( b )" := (Lw a b 4 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 8( b )" := (Lw a b 8 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 12( b )" := (Lw a b 12 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 16( b )" := (Lw a b 16 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 20( b )" := (Lw a b 20 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 24( b )" := (Lw a b 24 : insn) (at level 10) : otbn_scope.
  Notation "'lw' a , 28( b )" := (Lw a b 28 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 0( b )" := (Sw a b 0 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 4( b )" := (Sw a b 4 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 8( b )" := (Sw a b 8 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 12( b )" := (Sw a b 12 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 16( b )" := (Sw a b 16 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 20( b )" := (Sw a b 20 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 24( b )" := (Sw a b 24 : insn) (at level 10) : otbn_scope.
  Notation "'sw' a , 28( b )" := (Sw a b 28 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 0( b )" := (Bn_lid a b 0 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 32( b )" := (Bn_lid a b 32 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 64( b )" := (Bn_lid a b 64 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 96( b )" := (Bn_lid a b 96 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 128( b )" := (Bn_lid a b 128 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 160( b )" := (Bn_lid a b 160 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 192( b )" := (Bn_lid a b 192 : insn) (at level 10) : otbn_scope.
  Notation "'bn.lid' a , 224( b )" := (Bn_lid a b 224 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 0( b )" := (Bn_sid a b 0 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 32( b )" := (Bn_sid a b 32 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 64( b )" := (Bn_sid a b 64 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 96( b )" := (Bn_sid a b 96 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 128( b )" := (Bn_sid a b 128 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 160( b )" := (Bn_sid a b 160 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 192( b )" := (Bn_sid a b 192 : insn) (at level 10) : otbn_scope.
  Notation "'bn.sid' a , 224( b )" := (Bn_sid a b 224 : insn) (at level 10) : otbn_scope.

  (* pseudo-instructions *)
  Notation "'nop'" := (Addi x0 x0 0 : insn) (at level 40) : otbn_scope.

  (* Control instructions. *)
  Notation "'ret'" := (Ret : insn) (at level 40) : otbn_scope.
  Notation "'ecall'" := (Ecall : insn) (at level 40) : otbn_scope.
  Notation "'unimp'" := (Unimp : insn) (at level 40) : otbn_scope.
  Notation "'jal' a , addr" := (Jal a addr : insn) (at level 40) : otbn_scope.
  Notation "'bne' a , b , addr" := (Bne a b addr : insn) (at level 40) : otbn_scope.
  Notation "'beq' a , b , addr" := (Beq a b addr : insn) (at level 40) : otbn_scope.
  Notation "'loop' a" := (Loop a : insn) (at level 40) : otbn_scope.
  Notation "'loopi' a" := (Loopi a : insn) (at level 40) : otbn_scope.
  Notation "'loopend'" := (LoopEnd : insn) (at level 40) : otbn_scope.

  (* Tests for instruction notations. *)
  Local Definition tests : list (insn (label:=nat)) := [
      addi x3, x0, 5
      ; addi x3, x0, 0
      ; addi x3, x0, -5
      ; addi x3, x0, -1600
      ; lui x2, 2
      ; add x2, x3, x4
      ; sub x2, x3, x4
      ; sll x2, x3, x4
      ; slli x2, x3, 4
      ; srl x2, x3, x4
      ; srli x2, x3, 4
      ; sra x2, x3, x4
      ; srai x2, x3, 4
      ; and x2, x3, x4
      ; andi x2, x3, 4
      ; xor x2, x3, x4
      ; xori x2, x3, 4
      ; or x2, x3, x4
      ; ori x2, x3, 4
      ; lw x29, 0(x28)
      ; sw x29, 16(x28)
      ; csrrs x2, CSR_RND, x3
      ; csrrw x2, CSR_RND, x3
      ; bn.and w2, w3, w4, FG0
      ; bn.and w2, w3, w4 << 16, FG0
      ; bn.and w2, w3, w4 >> 0x2, FG1
      ; bn.xor w2, w3, w4, FG0
      ; bn.xor w2, w3, w4 << 16, FG0
      ; bn.xor w2, w3, w4 >> 0x2, FG1
      ; bn.or w2, w3, w4, FG0
      ; bn.or w2, w3, w4 << 16, FG0
      ; bn.or w2, w3, w4 >> 0x2, FG1
      ; bn.not w2, w3, FG0
      ; bn.not w2, w3 << 16, FG0
      ; bn.not w2, w3 >> 0x2, FG1
      ; bn.rshi w27, w28, w29 >> 255
      ; bn.sel w0, w1, w2, FG0.M
      ; bn.sel w0, w1, w2, FG1.M
      ; bn.sel w0, w1, w2, FG0.L
      ; bn.sel w0, w1, w2, FG1.L
      ; bn.sel w0, w1, w2, FG0.Z
      ; bn.sel w0, w1, w2, FG1.C
      ; bn.cmp w0, w0, FG0
      ; bn.cmp w20, w20 << 128, FG0
      ; bn.cmp w20, w20 >> 128, FG1
      ; bn.cmpb w0, w0, FG0
      ; bn.cmpb w20, w20 << 128, FG0
      ; bn.cmpb w20, w20 >> 128, FG1
      ; bn.add w0, w0, w0, FG0
      ; bn.add w20, w20, w20 << 128, FG0
      ; bn.add w20, w20, w20 >> 128, FG1
      ; bn.addc w0, w0, w0, FG0
      ; bn.addc w20, w20, w20 << 128, FG0
      ; bn.addc w20, w20, w20 >> 128, FG1
      ; bn.addi w0, w0, 0, FG0
      ; bn.addi w0, w0, 0x1234, FG0
      ; bn.sub w0, w0, w0, FG0
      ; bn.sub w20, w20, w20 << 128, FG0
      ; bn.sub w20, w20, w20 >> 128, FG1
      ; bn.subb w0, w0, w0, FG0
      ; bn.subb w20, w20, w20 << 128, FG0
      ; bn.subb w20, w20, w20 >> 128, FG1
      ; bn.subi w20, w20, 20, FG0
      ; bn.subi w20, w20, 0xffff, FG1
      ; bn.addm w0, w1, w2
      ; bn.subm w0, w1, w2
      ; bn.mulqacc w2.0, w3.0, 0
      ; bn.mulqacc w2.0, w3.3, 64
      ; bn.mulqacc.z w2.0, w3.3, 64
      ; bn.mulqacc.wo w4, w2.0, w3.3, 64
      ; bn.mulqacc.wo.z w4, w2.0, w3.3, 64
      ; bn.mulqacc.so w4.L, w2.0, w3.3, 64
      ; bn.mulqacc.so w4.U, w2.0, w3.3, 64
      ; bn.mulqacc.so.z w4.L, w2.0, w3.3, 128
      ; bn.mulqacc.so.z w4.U, w2.0, w3.3, 192
      ; bn.movr x20, x21
      ; bn.movr x20++, x21
      ; bn.movr x20, x21++
      ; bn.mov w20, w21
      ; bn.lid x20, 0(x21)
      ; bn.lid x20, 32(x21++)
      ; bn.lid x20++, 64(x21)
      ; bn.sid x20, 96(x21)
      ; bn.sid x20, 128(x21++)
      ; bn.sid x20++, 160(x21)
      ; bn.wsrr w0, WSR_MOD
      ; bn.wsrw WSR_ACC, w1
      ; bne x3, x4, 0xfde
      ; beq x3, x4, 0x400
      ; loop x2
      ; loopi 2
      ; loopend
      ; ret
      ; ecall
      ; nop
      ; unimp
    ]%otbn.
End Notations.

