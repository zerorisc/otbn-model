Require Import Coq.ZArith.ZArith.


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
| flagC : bool -> flag.

Definition flag_group : Type := bool.
Definition FG0 : flag_group := false.
Definition FG1 : flag_group := true.  

(* Straightline instructions (no control flow) *)
Inductive sinsn : Type :=
| Addi : gpr -> gpr -> Z -> sinsn
| Add : gpr -> gpr -> gpr -> sinsn
| Lw : gpr -> gpr -> Z -> sinsn
| Sw : gpr -> gpr -> Z -> sinsn
| Csrrs : csr -> gpr -> sinsn
| Bn_add : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_addc : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_addi : wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_and : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_xor : wdr -> wdr -> wdr -> Z -> flag_group -> sinsn
| Bn_lid : gpr -> bool -> gpr -> bool -> Z -> sinsn
| Bn_sid : gpr -> bool -> gpr -> bool -> Z -> sinsn
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
