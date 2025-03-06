Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import Otbn.ISA.ISA.
Require Import Otbn.ISA.Labels.
Require Coq.Strings.HexString.
Local Open Scope Z_scope.

Section __.
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

  Definition flag_group_to_string (group : flag_group) : string :=
    if group then "FG1" else "FG0".

  Definition flag_to_string (f : flag) : string :=
    match f with
    | flagM g => flag_group_to_string g ++ ".M"
    | flagL g => flag_group_to_string g ++ ".L"
    | flagZ g => flag_group_to_string g ++ ".Z"
    | flagC g => flag_group_to_string g ++ ".C"
    end.

  Definition shift_to_string (shift : Z) : string :=
    if shift =? 0
    then ""
    else (if shift >? 0 then " <<" else " >>") ++ HexString.of_Z (Z.abs shift).

  Definition inc_to_string (inc : bool) : string :=
    if inc then "++" else "".

  Definition sinsn_to_string (i : sinsn) : string :=
    match i with
    | Addi rd rs imm =>
        "addi " ++ rd ++ ", " ++ rs ++ ", " ++ HexString.of_Z imm
    | Add rd rs1 rs2 =>
        "add " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Lw rd rs imm =>
        "lw " ++ rd ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs
    | Sw rs1 rs2 imm =>
        "sw " ++ rs2 ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs1
    | Csrrs rd rs =>
        "csrrs " ++ rd ++ ", " ++ rs ++ ", "
    | Bn_add wrd wrs1 wrs2 shift fg =>
        "bn.add " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_addc wrd wrs1 wrs2 shift fg =>
        "bn.addc " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_addi wrd wrs1 imm fg =>
        "bn.addi " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ HexString.of_Z imm ++ ", " ++ flag_group_to_string fg
    | Bn_xor wrd wrs1 wrs2 shift fg =>
        "bn.xor " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_and wrd wrs1 wrs2 shift fg =>
        "bn.and " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_lid grd grd_inc grs1 grs1_inc imm =>
        "bn.lid " ++ grd ++ inc_to_string grd_inc ++ ", (" ++ HexString.of_Z imm ++ ")" ++ grs1 ++ inc_to_string grs1_inc
    | Bn_sid grs2 grs2_inc grs1 grs1_inc imm =>
        "bn.sid " ++ grs2 ++ inc_to_string grs2_inc ++ ", (" ++ HexString.of_Z imm ++ ")" ++ grs1 ++ inc_to_string grs1_inc
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
End __.
