Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Datatypes.String.
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

  Definition limb_to_string (l : limb) : string :=
    wdr_to_string (fst l) ++ "." ++ String.of_nat (Z.to_nat (snd l)).

  Definition shift_to_string (shift : Z) : string :=
    if shift =? 0
    then ""
    else (if shift >? 0 then " <<" else " >>") ++ HexString.of_Z (Z.abs shift).

  Definition inc_to_string (inc : gpr_inc) : string :=
    match inc with
    | gpr_inc_false r => gpr_to_string r
    | gpr_inc_true r => gpr_to_string r ++ "++"
    end.

  Definition imm_to_dec (imm : Z) :=
    (if (0 <? imm)%Z then "-" else "" ++ String.of_nat (Z.to_nat (Z.abs imm)))%string.

  Definition sinsn_to_string (i : sinsn) : string :=
    match i with
    | Addi rd rs imm =>
        "addi " ++ rd ++ ", " ++ rs ++ ", " ++ HexString.of_Z imm
    | Lui rd imm =>
        "lui " ++ rd ++ ", " ++ HexString.of_Z imm
    | Add rd rs1 rs2 =>
        "add " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Sub rd rs1 rs2 =>
        "sub " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Sll rd rs1 rs2 =>
        "sll " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Slli rd rs1 imm =>
        "slli " ++ rd ++ ", " ++ rs1 ++ ", " ++ imm_to_dec imm
    | Srl rd rs1 rs2 =>
        "srl " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Srli rd rs1 imm =>
        "srli " ++ rd ++ ", " ++ rs1 ++ ", " ++ imm_to_dec imm
    | Sra rd rs1 rs2 =>
        "sra " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Srai rd rs1 imm =>
        "srai " ++ rd ++ ", " ++ rs1 ++ ", " ++ imm_to_dec imm
    | And rd rs1 rs2 =>
        "and " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Andi rd rs1 imm =>
        "andi " ++ rd ++ ", " ++ rs1 ++ ", " ++ HexString.of_Z imm
    | Or rd rs1 rs2 =>
        "or " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Ori rd rs1 imm =>
        "ori " ++ rd ++ ", " ++ rs1 ++ ", " ++ HexString.of_Z imm
    | Xor rd rs1 rs2 =>
        "xor " ++ rd ++ ", " ++ rs1 ++ ", " ++ rs2
    | Xori rd rs1 imm =>
        "xori " ++ rd ++ ", " ++ rs1 ++ ", " ++ HexString.of_Z imm
    | Lw rd rs imm =>
        "lw " ++ rd ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs
    | Sw rs1 rs2 imm =>
        "sw " ++ rs2 ++ ", (" ++ HexString.of_Z imm ++ ")" ++ rs1
    | Csrrs rd cs1 rs =>
        "csrrs " ++ rd ++ ", " ++ cs1 ++ ", " ++ rs
    | Csrrw rd cs1 rs =>
        "csrrs " ++ rd ++ ", " ++ cs1 ++ ", " ++ rs
    | Bn_and wrd wrs1 wrs2 shift fg =>
        "bn.and " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_or wrd wrs1 wrs2 shift fg =>
        "bn.or " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_xor wrd wrs1 wrs2 shift fg =>
        "bn.xor " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_not wrd wrs1 shift fg =>
        "bn.not " ++ wrd ++ ", " ++ wrs1 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_rshi wrd wrs1 wrs2 imm =>
        "bn.rshi " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ " << " ++ imm_to_dec imm
    | Bn_sel wrd wrs1 wrs2 f =>
        "bn.sel " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ ", " ++ flag_to_string f
    | Bn_cmp wrs1 wrs2 shift fg =>
        "bn.cmp " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_cmpb wrs1 wrs2 shift fg =>
        "bn.cmpb " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_add wrd wrs1 wrs2 shift fg =>
        "bn.add " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_addc wrd wrs1 wrs2 shift fg =>
        "bn.addc " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_addi wrd wrs1 imm fg =>
        "bn.addi " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ HexString.of_Z imm ++ ", " ++ flag_group_to_string fg
    | Bn_sub wrd wrs1 wrs2 shift fg =>
        "bn.sub " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_subb wrd wrs1 wrs2 shift fg =>
        "bn.subb " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2 ++ shift_to_string shift ++ ", " ++ flag_group_to_string fg
    | Bn_subi wrd wrs1 imm fg =>
        "bn.subi " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ HexString.of_Z imm ++ ", " ++ flag_group_to_string fg
    | Bn_addm wrd wrs1 wrs2 =>
        "bn.addm " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2
    | Bn_subm wrd wrs1 wrs2 =>
        "bn.subm " ++ wrd ++ ", " ++ wrs1 ++ ", " ++ wrs2
    | Bn_mulqacc z wrs1 wrs2 imm  =>
        "bn.mulqacc" ++ if z then ".z" else "" ++ " " ++ limb_to_string wrs1 ++ ", " ++ limb_to_string wrs2 ++ "<<" ++ imm_to_dec imm
    | Bn_mulqacc_wo z wrd wrs1 wrs2 imm  =>
        "bn.mulqacc.wo" ++ if z then ".z" else "" ++ " " ++ wdr_to_string wrd ++ ", " ++ limb_to_string wrs1 ++ ", " ++ limb_to_string wrs2 ++ "<<" ++ imm_to_dec imm
    | Bn_mulqacc_so z wrd U wrs1 wrs2 imm  =>
        "bn.mulqacc.wo" ++ if z then ".z" else "" ++ " " ++ wdr_to_string wrd ++ if U then ".U" else ".L" ++ ", " ++ limb_to_string wrs1 ++ ", " ++ limb_to_string wrs2 ++ "<<" ++ imm_to_dec imm
    | Bn_lid grd_inc grs1_inc imm =>
        "bn.lid " ++ inc_to_string grd_inc ++ ", (" ++ HexString.of_Z imm ++ ")" ++ inc_to_string grs1_inc
    | Bn_sid grs2_inc grs1_inc imm =>
        "bn.sid " ++ inc_to_string grs2_inc ++ ", (" ++ HexString.of_Z imm ++ ")" ++ inc_to_string grs1_inc
    | Bn_mov wrd wrs1 =>
        "bn.mov " ++ wdr_to_string wrd ++ ", " ++ wdr_to_string wrs1
    | Bn_movr grd_inc grs1_inc =>
        "bn.movr " ++ inc_to_string grd_inc ++ ", " ++ inc_to_string grs1_inc
    | Bn_wsrr wrd wrs1 =>
        "bn.wsrr " ++ wdr_to_string wrd ++ ", " ++ wsr_to_string wrs1
    | Bn_wsrw wsd wrs1 =>
        "bn.wsrw " ++ wsr_to_string wsd ++ ", " ++ wdr_to_string wrs1
    end.

  Definition cinsn_to_string (i : cinsn (label:=label)) : string :=
    match i with
    | Ret => "ret"
    | Ecall => "ecall"
    | Unimp => "unimp"
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
