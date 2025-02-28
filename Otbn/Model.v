Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Semantics.OmniSmallstepCombinators.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import coqutil.Z.ZLib.
Require Coq.Strings.HexString.
Import ListNotations.
Local Open Scope Z_scope.

(*** Model of OTBN. ***)

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
  Local Ltac prove_eqb_spec r1 r2 :=
    destruct r1, r2; constructor; congruence.
  
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

  Definition wdr_eqb (r1 r2 : wdr) : bool.
  Proof. derive_eqb r1 r2. Defined.
  Definition wsr_eqb (r1 r2 : wsr) : bool.
  Proof. derive_eqb r1 r2. Defined.
  Definition wreg_eqb (r1 r2 : wreg) : bool :=
    match r1, r2 with
    | wdreg r1, wdreg r2 => wdr_eqb r1 r2
    | wsreg r1, wsreg r2 => wsr_eqb r1 r2
    | _, _ => false
    end.

  Global Instance wdr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wdr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Global Instance wsr_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wsr_eqb r1 r2).
  Proof. prove_eqb_spec r1 r2. Qed.
  Global Instance wreg_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (wreg_eqb r1 r2).
  Proof.
    destruct r1, r2; cbn [wreg_eqb];
      repeat lazymatch goal with
      | |- BoolSpec _ _ (?eqb ?x ?y) => destr (eqb x y)
      | _ => constructor; congruence
        end.
  Qed.

  Definition flag_group_eqb (fg1 fg2 : flag_group) : bool.
  Proof. derive_eqb fg1 fg2. Defined.
  Definition flag_eqb (f1 f2 : flag) : bool :=
    match f1, f2 with
    | flagM fg1, flagM fg2 => flag_group_eqb fg1 fg2
    | flagL fg1, flagL fg2 => flag_group_eqb fg1 fg2
    | flagZ fg1, flagZ fg2 => flag_group_eqb fg1 fg2
    | flagC fg1, flagC fg2 => flag_group_eqb fg1 fg2
    | _, _ => false
    end.

  Global Instance flag_group_eqb_spec :
    forall fg1 fg2, BoolSpec (fg1 = fg2) (fg1 <> fg2) (flag_group_eqb fg1 fg2).
  Proof. prove_eqb_spec fg1 fg2. Qed.
  Global Instance flag_eqb_spec : forall f1 f2, BoolSpec (f1 = f2) (f1 <> f2) (flag_eqb f1 f2).
  Proof.
    destruct f1, f2; cbn [flag_eqb];
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
    {mem : map.map word32 byte}
    {fetch : label * nat -> option (insn (label:=label))}.

  Definition advance_pc (pc : label * nat) := (fst pc, S (snd pc)).

  Definition is_valid_addi_imm (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_bn_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 1023).
  Definition is_valid_mem_offset (imm : Z) : bool :=
    (-2048 <=? imm) && (imm <=? 2047).
  Definition is_valid_wide_mem_offset (imm : Z) : bool :=
    (-16384 <=? imm) && (imm <=? 16352) && (imm mod 32 =? 0).
  Definition is_word_aligned width (addr : word32) : bool :=
    word.eqb (word.of_Z 0) (word.and addr (word.of_Z (Z.ones width))).
  Definition is_valid_shift_imm (imm : Z) : bool :=
    (0 <=? imm) && (imm <=? 248) && (imm mod 8 =? 0).

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

    Definition read_wdr (wregs : wregfile) (r : wdr) (P : word256 -> T) : T :=
     option_bind (map.get wregs (wdreg r))
       ("Register " ++ wdr_to_string r ++ " read but not set.")
       P.

    Definition read_flag (flags : flagfile) (f : flag) (P : bool -> T) : T :=
      option_bind (map.get flags f)
        ("Flag " ++ flag_to_string f ++ " read but not set") P.

    Definition lookup_wdr (i : word32) (P : wdr -> T) : T :=
      let i := Z.to_nat (word.unsigned (word.and i (word.of_Z 31))) in
      (match i with
       | 0 => P w0
       | 1 => P w1
       | 2 => P w2
       | 3 => P w3
       | 4 => P w4
       | 5 => P w5
       | 6 => P w6
       | 7 => P w7
       | 8 => P w8
       | 9 => P w9
       | 10 => P w10
       | 11 => P w11
       | 12 => P w12
       | 13 => P w13
       | 14 => P w14
       | 15 => P w15
       | 16 => P w16
       | 17 => P w17
       | 18 => P w18
       | 19 => P w19
       | 20 => P w20
       | 21 => P w21
       | 22 => P w22
       | 23 => P w23
       | 24 => P w24
       | 25 => P w25
       | 26 => P w26
       | 27 => P w27
       | 28 => P w28
       | 29 => P w29
       | 30 => P w30
       | 31 => P w31
       | _ => err ("Invalid wide register lookup: " ++ HexString.of_nat i)
       end)%nat.

    Definition read_wdr_indirect
      (i : word32) (wregs : wregfile) (P : word256 -> T) : T :=
      lookup_wdr i
        (fun w =>
           read_wdr wregs w P).
                     

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
      if is_word_aligned width addr
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
      lookup_wdr i
        (fun w => write_wdr wregs w v P).

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
      | CSR_FG0 => write_flag_group FG0 flags v (fun flags => P regs flags)
      | CSR_FG1 => write_flag_group FG1 flags v (fun flags => P regs flags)
      | CSR_FLAGS =>
          write_flag_group FG0 flags v
            (fun flags =>
               write_flag_group FG1 flags (word.sru v (word.of_Z 4))
                 (fun flags => P regs flags))
      | CSR_RND_PREFETCH => P regs flags (* no effect on this model *)
      | CSR_RND => P regs flags (* writes ignored *)
      | CSR_URND => P regs flags (* writes ignored *)
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
      if is_word_aligned width addr
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

    Definition carry_bit (x : Z) := x >? (2^256).
    Definition borrow_bit (x : Z) := x <? 0.

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
                    load_word dmem (word.add vx (word.of_Z imm))
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
                          store_word dmem (word.add vx (word.of_Z imm)) vy
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
      | Bn_add d x y s fg =>
          read_wdr wregs x
            (fun vx =>
               read_wdr wregs y
               (fun vy =>
                  apply_shift vy s
                    (fun vy =>
                       let result := word.add vx vy in
                       write_wdr wregs d result
                         (fun wregs =>
                            write_flag flags (flagC fg)
                              (carry_bit (word.unsigned vx + word.unsigned vy))
                              (fun flags =>
                                 update_mlz flags fg result
                                   (fun flags => post regs wregs flags dmem))))))
      | Bn_addc d x y s fg =>
          read_wdr wregs x
            (fun vx =>
               read_wdr wregs y
               (fun vy =>
                  apply_shift vy s
                    (fun vy =>
                       read_flag flags (flagC fg)
                         (fun c =>
                            let result := word.add (word.add vx vy) (word.of_Z (Z.b2z c)) in
                            write_wdr wregs d result
                              (fun wregs =>
                                 write_flag flags (flagC fg)
                                   (carry_bit (word.unsigned vx + word.unsigned vy + Z.b2z c))
                                   (fun flags =>
                                      update_mlz flags fg result
                                        (fun flags => post regs wregs flags dmem)))))))
      | Bn_addi d x imm fg =>
          if is_valid_bn_imm imm
          then
            read_wdr wregs x
              (fun vx =>
                 let result := word.add vx (word.of_Z imm) in
                 write_wdr wregs d result
                   (fun wregs =>
                      write_flag flags (flagC fg)
                        (carry_bit (word.unsigned vx + imm))
                        (fun flags =>
                           update_mlz flags fg result
                             (fun flags => post regs wregs flags dmem))))
          else err ("Invalid immediate for BN.ADDI: " ++ HexString.of_Z imm)
      | Bn_and d x y s fg =>
          read_wdr wregs x
            (fun vx =>
               read_wdr wregs y
               (fun vy =>
                  apply_shift vy s
                    (fun vy =>
                       let result := word.xor vx vy in
                       write_wdr wregs d result
                         (fun wregs =>
                            update_mlz flags fg result
                              (fun flags => post regs wregs flags dmem)))))
      | Bn_xor d x y s fg =>
          read_wdr wregs x
            (fun vx =>
               read_wdr wregs y
               (fun vy =>
                  apply_shift vy s
                    (fun vy =>
                       let result := word.xor vx vy in
                       write_wdr wregs d result
                         (fun wregs =>
                            update_mlz flags fg result
                              (fun flags => post regs wregs flags dmem)))))
      | Bn_lid d dinc x xinc imm =>
          if is_valid_wide_mem_offset imm
          then
            read_gpr regs x
              (fun vx =>
                 let addr := (word.add vx (word.of_Z imm)) in
                 load_word dmem addr
                   (fun vm =>
                      read_gpr regs d
                        (fun vd => 
                           write_wdr_indirect vd wregs vm
                             (fun wregs =>
                                if dinc
                                then if xinc
                                     then err ("Both increment bits set for BN.LID.")
                                     else
                                       write_gpr regs d (word.add vd (word.of_Z 1))
                                         (fun regs => post regs wregs flags dmem)
                                else if xinc
                                     then 
                                       write_gpr regs x (word.add vx (word.of_Z 32))
                                         (fun regs => post regs wregs flags dmem)
                                     else  post regs wregs flags dmem))))
          else err ("Invalid memory offset for BN.LID: " ++ HexString.of_Z imm)
      | Bn_sid x xinc y yinc imm =>
          if is_valid_wide_mem_offset imm
          then
            read_gpr regs x
              (fun ix =>
                 read_wdr_indirect ix wregs
                 (fun vx =>
                    read_gpr regs y
                      (fun vy =>
                         let addr := (word.add vy (word.of_Z imm)) in
                         store_word dmem addr vx
                           (fun dmem =>
                              if xinc
                              then if yinc
                                   then err ("Both increment bits set for BN.SID.")
                                   else
                                     write_gpr regs x (word.add ix (word.of_Z 1))
                                       (fun regs => post regs wregs flags dmem)
                              else if yinc
                                   then 
                                     write_gpr regs y (word.add vy (word.of_Z 32))
                                       (fun regs => post regs wregs flags dmem)
                                   else  post regs wregs flags dmem))))
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

Module Coercions.
  Coercion Straightline : sinsn >-> insn.
  Coercion Control : cinsn >-> insn.
End Coercions.
Import Coercions.

Require Import coqutil.Map.SortedListZ.
Require Import coqutil.Map.SortedListString.

(* Contains a way to link programs. *)
Section Build.           
  Definition symbols : map.map string nat := SortedListString.map _.
  (* Functions consist of a name, internal labels (map of string ->
     offset within the function), and a list of instructions. *)
  Definition otbn_function : Type := string * symbols * list (insn (label:=string)).
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
    (syms_offset : symbols * nat) (fn : otbn_function) : maybe (symbols * nat) :=
    let fn_name := fst (fst fn) in
    let fn_syms := snd (fst fn) in
    let fn_insns := snd fn in
    (syms <- add_symbol (fst syms_offset) fn_name (snd syms_offset) ;
     syms <- merge_symbols (snd syms_offset) syms fn_syms ;
     Ok (syms, (snd syms_offset + length fn_insns)%nat)).
  Definition link_symbols'
    (start_syms : symbols)
    (start_offset : nat)
    (fns : list otbn_function)
    : maybe (symbols * nat) :=
    maybe_fold_left link_symbols_for_function fns (start_syms, start_offset).
  Definition link_symbols (fns : list otbn_function) : maybe symbols :=
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
    (syms : symbols) (prog : program) (fn : otbn_function) : maybe program :=
    (fn_insns <- link_insns syms (snd fn) ;
     Ok (prog ++ fn_insns)).

  Definition link (fns : list otbn_function) : maybe program :=
    (syms <- link_symbols fns ;
     maybe_fold_left (link' syms) fns []).

  Definition get_label_offset
    (fn : otbn_function) (label : string) : option nat :=
    let fn_name := fst (fst fn) in
    let fn_syms := snd (fst fn) in
    if (String.eqb label fn_name)
    then Some 0%nat
    else map.get fn_syms label.

  (* Fetch from a function. *)
  Definition fetch_fn
    (fn : otbn_function) (pc : string * nat) : option insn :=
    let label := fst pc in
    let offset := snd pc in
    let fn_insns := snd fn in
    match get_label_offset fn label with
    | None => None
    | Some label_offset => nth_error fn_insns (label_offset + offset)
    end.
 
  (* Fetch from a collection of functions. *)
  Definition fetch_ctx
    (fns : list otbn_function) (pc : string * nat) : option insn :=
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
    (fn : otbn_function) (global_offset : nat) : Prop :=
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
  Context {flagfile : map.map flag bool} {mem : map.map word32 byte}.

  (* Returns the overall size of the program containing the functions
     and starting at the given offset. *)
  Definition program_size (start : nat) (fns : list otbn_function) : nat :=
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

  Lemma fetch_fn_name offset (fn : otbn_function) :
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
      cbv [otbn_function] in *; destruct_products; cbn [fst snd] in *.
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

  Lemma read_wdr_weaken wregs r P Q :
    read_wdr wregs r P ->
    (forall wregs, P wregs -> Q wregs) ->
    read_wdr wregs r Q.
  Proof.
    cbv [read_wdr err option_bind proof_semantics]; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | |- Q _ => solve [eauto]
        end.
  Qed.

  Lemma read_flag_weaken flags f P Q :
    read_flag flags f P ->
    (forall flags, P flags -> Q flags) ->
    read_flag flags f Q.
  Proof.
    cbv [read_flag err option_bind proof_semantics]; intros;
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
    cbv [read_csr read_flag read_flag_group err random urandom option_bind proof_semantics];
      intros.
    destruct r;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma load_byte_weaken dmem addr P Q :
    load_byte (T:=Prop) dmem addr P ->
    (forall x, P x -> Q x) ->
    load_byte (T:=Prop) dmem addr Q.
  Proof.
    cbv [load_byte err option_bind proof_semantics]; destruct_one_match; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma load_bytes_weaken dmem addr len P Q :
    load_bytes (T:=Prop) dmem addr len P ->
    (forall x, P x -> Q x) ->
    load_bytes (T:=Prop) dmem addr len Q.
  Proof.
    intros; generalize dependent addr. generalize dependent P. generalize dependent Q.
    induction len; cbn [load_bytes]; [ solve [auto] | ].
    intros. eapply load_byte_weaken; [ eassumption | ].
    cbv beta; intros. eapply IHlen; eauto; [ ].
    cbv beta; eauto.
  Qed.

  Lemma load_word_weaken {width} {word} dmem addr P Q :
    load_word (width:=width) (word:=word) dmem addr P ->
    (forall x, P x -> Q x) ->
    load_word (width:=width) (word:=word) dmem addr Q.
  Proof.
    cbv [load_word]. destruct_one_match; eauto; [ ].
    intros. eapply load_bytes_weaken; eauto.
  Qed.

  Lemma store_byte_weaken dmem addr v P Q :
    store_byte (T:=Prop) dmem addr v P ->
    (forall x, P x -> Q x) ->
    store_byte (T:=Prop) dmem addr v Q.
  Proof.
    cbv [store_byte err option_bind proof_semantics]; destruct_one_match; intros;
      repeat lazymatch goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H : False |- _ => contradiction H
        | |- exists _, _ => eexists; ssplit; [ eassumption | ]
        | _ => solve [eauto]
        end.
  Qed.

  Lemma store_bytes_weaken dmem addr bs P Q :
    store_bytes (T:=Prop) dmem addr bs P ->
    (forall x, P x -> Q x) ->
    store_bytes (T:=Prop) dmem addr bs Q.
  Proof.
    intros; generalize dependent addr. generalize dependent dmem.
    generalize dependent P. generalize dependent Q.
    induction bs; cbn [store_bytes]; [ solve [auto] | ].
    intros. eapply store_byte_weaken; [ eassumption | ].
    cbv beta; intros. eapply IHbs; eauto.
  Qed.

  Lemma store_word_weaken {width} {word} dmem addr v P Q :
    store_word (T:=Prop) (width:=width) (word:=word) dmem addr v P ->
    (forall x, P x -> Q x) ->
    store_word (T:=Prop) (width:=width) (word:=word) dmem addr v Q.
  Proof.
    cbv [store_word]. destruct_one_match; eauto; [ ].
    intros. eapply store_bytes_weaken; eauto.
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

  Lemma write_wdr_weaken wregs r v P Q :
    write_wdr (T:=Prop) wregs r v P ->
    (forall wregs, P wregs -> Q wregs) ->
    write_wdr (T:=Prop) wregs r v Q.
  Proof.
    cbv [write_wdr write_flag_group extract_flag]; intros. eauto.
  Qed.

  Lemma write_csr_weaken regs flags r v P Q :
    write_csr (T:=Prop) regs flags r v P ->
    (forall regs flags, P regs flags -> Q regs flags) ->
    write_csr (T:=Prop) regs flags r v Q.
  Proof.
    cbv [write_csr write_flag_group extract_flag]; intros; destruct_one_match; eauto.
  Qed.

  Lemma apply_shift_weaken v shift P Q :
    apply_shift v shift P ->
    (forall v, P v -> Q v) ->
    apply_shift v shift Q.
  Proof.
    cbv [apply_shift]; intros; repeat destruct_one_match; eauto.
  Qed.

  Lemma write_flag_weaken flags f v P Q :
    write_flag (T:=Prop) flags f v P ->
    (forall flags, P flags -> Q flags) ->
    write_flag (T:=Prop) flags f v Q.
  Proof.
    cbv [write_flag]; intros; repeat destruct_one_match; eauto.
  Qed.

  Lemma update_mlz_weaken flags fg v P Q :
    update_mlz (T:=Prop) flags fg v P ->
    (forall flags, P flags -> Q flags) ->
    update_mlz (T:=Prop) flags fg v Q.
  Proof.
    cbv [update_mlz]; intros.
    repeat lazymatch goal with
           | |- write_flag _ _ _ _ =>
               eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
           | _ => solve [eauto]
           end.
  Qed.

  Lemma lookup_wdr_weaken i P Q :
    lookup_wdr (T:=Prop) i P ->
    (forall x, P x -> Q x) ->
    lookup_wdr (T:=Prop) i Q.
  Proof.
    cbv [lookup_wdr]; intros.
    repeat destruct_one_match; eauto.
  Qed.

  Lemma read_wdr_indirect_weaken i wregs P Q :
    read_wdr_indirect (T:=Prop) i wregs P ->
    (forall x, P x -> Q x) ->
    read_wdr_indirect (T:=Prop) i wregs Q.
  Proof.
    cbv [read_wdr_indirect]; intros.
    eapply lookup_wdr_weaken; [ eassumption | ].
    cbv beta; intros.
    eapply read_wdr_weaken; eauto.
  Qed.

  Lemma write_wdr_indirect_weaken i wregs v P Q :
    write_wdr_indirect (T:=Prop) i wregs v P ->
    (forall x, P x -> Q x) ->
    write_wdr_indirect (T:=Prop) i wregs v Q.
  Proof.
    cbv [write_wdr_indirect]; intros.
    eapply lookup_wdr_weaken; [ eassumption | ].
    cbv beta; intros.
    eapply write_wdr_weaken; eauto.
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
        | |- read_wdr _ _ _ =>
            eapply read_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_flag _ _ _ =>
            eapply read_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_byte _ _ _ =>
            eapply load_byte_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_bytes _ _ _ _ =>
            eapply load_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_word _ _ _ =>
            eapply load_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_byte _ _ _ _ =>
            eapply store_byte_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_bytes _ _ _ _ =>
            eapply store_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_word _ _ _ _ =>
            eapply store_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ =>
            eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wdr _ _ _ _ =>
            eapply write_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_csr _ _ _ _ _ =>
            eapply write_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- apply_shift _ _ _ =>
            eapply apply_shift_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_flag _ _ _ _ =>
            eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- update_mlz _ _ _ _ =>
            eapply update_mlz_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_wdr_indirect _ _ _ =>
            eapply read_wdr_indirect_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wdr_indirect _ _ _ _ =>
            eapply write_wdr_indirect_weaken; [ eassumption | ]; cbv beta; intros
        | |- if ?x then _ else _ => destr x
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
        | |- read_wdr _ _ _ =>
            eapply read_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_flag _ _ _ =>
            eapply read_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- read_csr _ _ _ _ =>
            eapply read_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_byte _ _ _ =>
            eapply load_byte_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_bytes _ _ _ _ =>
            eapply load_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- load_word _ _ _ =>
            eapply load_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_byte _ _ _ _ =>
            eapply store_byte_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_bytes _ _ _ _ =>
            eapply store_bytes_weaken; [ eassumption | ]; cbv beta; intros
        | |- store_word _ _ _ _ =>
            eapply store_word_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_gpr _ _ _ _ =>
            eapply write_gpr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_wdr _ _ _ _ =>
            eapply write_wdr_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_csr _ _ _ _ _ =>
            eapply write_csr_weaken; [ eassumption | ]; cbv beta; intros
        | |- apply_shift _ _ _ =>
            eapply apply_shift_weaken; [ eassumption | ]; cbv beta; intros
        | |- write_flag _ _ _ _ =>
            eapply write_flag_weaken; [ eassumption | ]; cbv beta; intros
        | |- update_mlz _ _ _ _ =>
            eapply update_mlz_weaken; [ eassumption | ]; cbv beta; intros
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

  Definition find_global_offset (fns : list otbn_function) (name : string) : option nat :=
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
    induction l1 as [|a ?]; intros; [ reflexivity | ].
    rewrite <-app_comm_cons. cbn [find].
    destruct_one_match; eauto.
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
        (fun offset (fn : otbn_function) => (offset + length (snd fn))%nat)
        fns start = (fold_left
                       (fun offset (fn : otbn_function) => (offset + length (snd fn))%nat)
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
    induction fns1; destruct fns2; intros *; rewrite ?app_nil_l, <-?app_comm_cons;
      cbn [app fold_left]; intros; subst;
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
    induction fns1; cbn [app]; intros; rewrite ?app_nil_l, <-?app_comm_cons in *;
      [ do 2 eexists; ssplit; [ reflexivity | eauto ] | ].
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

  Lemma clobbers_step_if l k v r1 r2 :
    clobbers l r1 r2 ->
    clobbers (if existsb (key_eqb k) l then l else k :: l) r1 (map.put r2 k v).
  Proof.
    intros.
    pose proof List.existsb_eqb_in k l.
    destr (existsb (key_eqb k) l).
    { apply clobbers_step_in; tauto. }
    { apply clobbers_step. auto. }
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

Notation bytes_at ptr bs := (eq (map.of_list_word_at ptr bs)) (only parsing).
Definition word_at {word32 : word.word 32} {mem : map.map word32 byte}
  {width} {word : word.word width}
  (ptr : word32) (v : word) : mem -> Prop :=
  bytes_at ptr (le_split (Z.to_nat (width / 8)) (word.unsigned v)).
Notation word32_at := (word_at (width:=32)) (only parsing).
Notation word256_at := (word_at (width:=256)) (only parsing).

(* Helper lemmas for proving things about programs. *)
Section Helpers.
  Context {word32 : word.word 32} {word32_ok : word.ok word32}.
  Context {word256 : word.word 256} {word256_ok : word.ok word256}.
  Context {regfile : map.map reg word32} {regfile_ok : map.ok regfile}.
  Context {wregfile : map.map wreg word256} {wregfile_ok : map.ok wregfile}.
  Context {flagfile : map.map flag bool} {flagfile_ok : map.ok flagfile}.
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.

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

  Definition function_symbols_disjoint (fn1 fn2 : otbn_function) : Prop :=
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

  Lemma is_word_aligned_imm width imm :
    0 <= width <= 32 ->
    is_word_aligned width (word.of_Z imm) = true <-> (imm mod 2^width = 0).
  Proof.
    cbv [is_word_aligned]. intros.
    pose proof Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia).
    assert (2^width <= 2^32) by (apply Z.pow_le_mono; lia).
    assert (0 <= Z.ones width < 2^32) by (rewrite Z.ones_equiv; split; lia).
    rewrite word.unsigned_eqb, Z.eqb_eq.
    rewrite word.unsigned_of_Z_0, word.unsigned_and.
    rewrite (word.unsigned_of_Z_nowrap (Z.ones width)) by lia.
    rewrite Z.land_ones by lia.
    rewrite word.unsigned_of_Z.
    cbv [word.wrap]. pose proof Z.mod_pos_bound (imm mod 2^32) (2^width) ltac:(lia).
    rewrite Z.mod_small by lia.
    replace (2^32) with (2^width * (2^(32-width)))
      by (rewrite <-Z.pow_add_r by lia; apply f_equal; lia).
    rewrite Z.rem_mul_r by lia.
    Z.push_mod. zsimplify. split; lia.
  Qed.

  Lemma is_word_aligned_0 width :
    0 <= width <= 32 ->
    is_word_aligned width (word.of_Z 0) = true.
  Proof.
    cbv [is_word_aligned]. intros. apply word.eqb_eq, word.unsigned_inj.
    rewrite word.unsigned_and, !word.unsigned_of_Z_0.
    rewrite Z.land_0_l. cbv [word.wrap]. rewrite Z.mod_0_l; lia.
  Qed.

  Lemma is_word_aligned_add width addr offset :
    0 <= width <= 32 ->
    is_word_aligned width addr = true ->
    is_word_aligned width offset = true ->
    is_word_aligned width (word.add addr offset) = true.
  Proof.
    cbv [is_word_aligned]; intros. apply word.eqb_eq.
    repeat lazymatch goal with
           | H : _ /\ _ |- _ => destruct H
           | H : word.eqb ?x ?y = true |- _ =>
               rewrite word.unsigned_eqb in H
           | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
           end.
    apply word.unsigned_inj.
    rewrite !word.unsigned_of_Z_0 in * by lia.
    rewrite !word.unsigned_and, !word.unsigned_add in *.
    pose proof Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia).
    assert (2^width <= 2^32) by (apply Z.pow_le_mono; lia).
    assert (0 <= Z.ones width < 2^32) by (rewrite Z.ones_equiv; split; lia).
    rewrite !word.unsigned_of_Z_nowrap in * by lia.
    rewrite !Z.land_ones in * by lia.
    cbv [word.wrap] in *.
    repeat lazymatch goal with
           | |- context [(?x mod 2^width) mod 2^32] =>
               pose proof Z.mod_pos_bound x (2^width) ltac:(lia);
               rewrite (Z.mod_small (x mod (2^width)) (2^32)) by lia
           | H: context [(?x mod 2^width) mod 2^32] |- _ =>
               pose proof Z.mod_pos_bound x (2^width) ltac:(lia);
               rewrite (Z.mod_small (x mod (2^width)) (2^32)) in H by lia
           end.
    replace (2^32) with (2^width * (2^(32-width)))
      by (rewrite <-Z.pow_add_r by lia; apply f_equal; lia).
    rewrite Z.rem_mul_r by lia.
    Z.push_mod. zsimplify.
    rewrite Z.add_mod by lia.
    repeat lazymatch goal with H : 0 = ?x |- context [?x] => rewrite <-H end.
    rewrite Z.mod_0_l by lia. reflexivity.
  Qed.

  (* TODO: put somewhere useful? *)
  Lemma put_iff1 {K V} {map : map.map K V} {map_ok : map.ok map}
                 {key_eqb : K -> K -> bool}
                 {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}
                 (m : map) k v :
    map.get m k = None -> Lift1Prop.iff1 (eq (map.put m k v)) (ptsto k v * eq m)%sep.
  Proof.
    repeat intro. cbv [sep ptsto]. split; intros; subst.
    { do 2 eexists; ssplit; eauto.
      eapply map.split_put_r2l; eauto; [ ].
      eapply map.split_empty_l; reflexivity. }
    { repeat lazymatch goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : map.split _ (map.put map.empty _ _) _ |- _ =>
                 apply map.split_put_l2r in H; [ | solve [apply map.get_empty ] ];
                 eapply map.split_empty_l in H
             | |- ?x = ?x => reflexivity
             | _ => progress subst
             end. }      
  Qed.
  
  (* complement of map.get_of_list_word_at_domain *)
  (* TODO: move to coqutil.Map.OfListWord *)
  Lemma map_get_of_list_word_at_None {width} {word : word width} {word_ok : word.ok word}
    {value : Type} {map : map.map word value} {map_ok : map.ok map} :
    forall (a : word) (xs : list value) (i : word),
      map.get (map.of_list_word_at a xs) i = None <->
        (word.unsigned (word.sub i a) < 0
         \/ Z.of_nat (length xs) <= word.unsigned (word.sub i a)).
  Proof.
    intros. pose proof word.unsigned_range (word.sub i a).
    rewrite map.get_of_list_word_at, nth_error_None.
    rewrite Nat2Z.inj_le, ?Znat.Z2Nat.id; intuition.
  Qed.

  Lemma map_of_list_word_at_get_pred {width} {word : word width} {word_ok : word.ok word}
    {value : Type} {map : map.map word value} {map_ok : map.ok map}
    (addr : word) (vs : list value) :
    Z.of_nat (length vs) < 2^width ->
    map.get (map.of_list_word_at (word.add addr (word.of_Z 1)) vs) addr = None.
  Proof.
    intros; pose proof word.width_pos.
    pose proof proj1 (Z.pow_gt_1 2 width ltac:(lia)) ltac:(lia).
    eapply map_get_of_list_word_at_None. right.
    rewrite word.unsigned_sub, word.unsigned_add, word.unsigned_of_Z_1.
    cbv [word.wrap]. Z.push_pull_mod.
    rewrite Z.sub_add_distr. zsimplify. rewrite Z.sub_0_l.
    rewrite Z.mod_opp_l_nz by (rewrite ?Z.mod_small by lia; lia).
    rewrite Z.mod_small by lia. lia.
  Qed.
    
  Lemma store_bytes_step dmem addr (bs : list byte) (P : mem -> Prop) old_bs R :
    word.unsigned addr + Z.of_nat (length bs) < DMEM_BYTES ->
    length old_bs = length bs ->
    (bytes_at addr old_bs * R)%sep dmem ->
    (forall dmem, (bytes_at addr bs * R)%sep dmem -> P dmem) ->
    store_bytes dmem addr bs P.
  Proof.
    pose proof word.unsigned_range addr.
    assert (DMEM_BYTES < 2^32) by (cbv [DMEM_BYTES]; lia).
    generalize dependent dmem. generalize dependent addr.
    generalize dependent P. generalize dependent R. generalize dependent old_bs.    
    induction bs; destruct old_bs; cbn [store_bytes length] in *; try lia;
      cbv [store_byte]; intros;
      repeat lazymatch goal with
        | H : context [map.of_list_word_at _ nil] |- _ =>
            rewrite map.of_list_word_nil in H
        | H : context [map.of_list_word_at _ (cons _ _)] |- _ =>
            rewrite map.of_list_word_at_cons in H
        | |- context [map.of_list_word_at _ nil] => rewrite map.of_list_word_nil
        | |- context [map.of_list_word_at _ (cons _ _)] => rewrite map.of_list_word_at_cons
        | H : length ?x = 0%nat |- _ => apply length_zero_iff_nil in H; subst
        | |- store_bytes _ _ bs _ =>
            eapply IHbs with (R:=sep R (ptsto _ _)) (old_bs:=old_bs); intros
        | H : forall m, _ -> ?P m |- ?P _ => eapply H
        | |- if ?x <? ?y then _ else _ => destr (x <? y); try lia
        | |- context [word.unsigned (word.add _ _)] => rewrite word.unsigned_add
        | |- context [word.unsigned (word.of_Z 1)] => rewrite word.unsigned_of_Z_1
        | |- context [word.wrap (word.unsigned ?addr + 1)] =>
            cbv [word.wrap]; rewrite Z.mod_small by lia
        | |- _ /\ _ => ssplit            
        | H : ?P |- ?P => exact H
        | _ => first [ progress extract_ex1_and_emp_in_hyps
                     | progress extract_ex1_and_emp_in_goal
                     | lazymatch goal with
                       | |- _ < _ => lia
                       | |- _ <= _ => lia
                       | |- length _ = length _ => lia
                       | _ => fail
                       end ]
        end.
    { apply sep_assoc, sep_comm. eapply sep_put.
      use_sep_assumption. rewrite put_iff1; [ ecancel | ].
      eapply map_of_list_word_at_get_pred. lia. }
    { seprewrite put_iff1; [ | use_sep_assumption; ecancel ].
      eapply map_of_list_word_at_get_pred. lia. }
  Qed.
  
  Lemma store_word_step
    {width} {word : word.word width} {word_ok : word.ok word}
    dmem addr (v old_v : word) (P : mem -> Prop) R :
    is_word_aligned width addr = true ->
    word.unsigned addr + width / 8 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.
    intros.
    pose proof word.width_pos (word:=word).
    cbv [store_word]. destruct_one_match; [ | congruence ].
    eapply store_bytes_step.
    { rewrite length_le_split.
      rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    { rewrite !length_le_split. reflexivity. }    
    { use_sep_assumption. cbv [word_at]. ecancel. }
    { intros. lazymatch goal with H : forall m, _ -> P m |- P _ => apply H end.
      use_sep_assumption. cbv [word_at]. ecancel. }
  Qed.
  
  Lemma store_word32_step
    dmem addr (v old_v : word32) (P : mem -> Prop) R :
    is_word_aligned 32 addr = true ->
    word.unsigned addr + 4 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.  intros; eapply store_word_step; eauto. Qed.
  
  Lemma store_word256_step
    dmem addr (v old_v : word256) (P : mem -> Prop) R :
    is_word_aligned 256 addr = true ->
    word.unsigned addr + 32 < DMEM_BYTES ->
    (word_at addr old_v * R)%sep dmem ->
    (forall dmem, (word_at addr v * R)%sep dmem -> P dmem) ->
    store_word dmem addr v P.
  Proof.  intros; eapply store_word_step; eauto. Qed.

  Lemma load_bytes_step dmem addr bs len (P : _ -> Prop) R :
    word.unsigned addr + Z.of_nat len < DMEM_BYTES ->
    (bytes_at addr bs * R)%sep dmem ->
    length bs = len ->
    P bs ->
    load_bytes dmem addr len P.
  Proof.
    assert (DMEM_BYTES < 2^32) by (cbv [DMEM_BYTES]; lia).
    generalize dependent addr. generalize dependent bs. generalize dependent P.
    generalize dependent R.
    induction len; destruct bs; cbn [load_bytes length] in *; try lia; eauto; [ ].
    intros. cbv [load_byte]. destruct_one_match; try lia; [ ].
    cbn [option_bind proof_semantics].
    pose proof word.unsigned_range addr.
    lazymatch goal with
      | H : sep (eq (map.of_list_word_at _ (_ :: _))) _ _ |- _ =>
          rewrite map.of_list_word_at_cons in H;
          seprewrite_in put_iff1 H
    end; [ | ].
    { eapply map_of_list_word_at_get_pred. lia. }
    { eexists.
      ssplit; [ eapply get_sep; use_sep_assumption; ecancel | ].
      eapply IHlen with (R:=sep _ R); try eassumption; try lia; [ | ].
      { rewrite word.unsigned_add, word.unsigned_of_Z_1.
        cbv [word.wrap]. rewrite Z.mod_small by lia. lia. }
      { use_sep_assumption. ecancel. } }
  Qed.

  Lemma load_word_step
    {width} {word : word.word width} {word_ok : word.ok word}
    dmem addr (v : word) (P : _ -> Prop) R :
    width mod 8 = 0 ->
    is_word_aligned width addr = true ->
    word.unsigned addr + width / 8 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof.
    intros. pose proof word.width_pos (word:=word).
    cbv [load_word]. destruct_one_match; [ | congruence ].
    eapply load_bytes_step.
    { rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    { use_sep_assumption. cbv [word_at]. ecancel. }
    { rewrite !length_le_split. reflexivity. }
    { intros. pose proof Z.div_pos width 8 ltac:(lia) ltac:(lia).
      rewrite le_combine_split. rewrite Z2Nat.id by lia.
      rewrite Z.div_mul_undo by lia.
      rewrite Z.mod_small by (apply word.unsigned_range).
      rewrite word.of_Z_unsigned. assumption. }
  Qed.

  Lemma load_word32_step dmem addr (v :word32) (P : _ -> Prop) R :
    is_word_aligned 32 addr = true ->
    word.unsigned addr + 4 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof. intros; eapply load_word_step; eauto. Qed.

  Lemma load_word256_step dmem addr (v :word256) (P : _ -> Prop) R :
    is_word_aligned 256 addr = true ->
    word.unsigned addr + 32 < DMEM_BYTES ->
    (word_at addr v * R)%sep dmem ->
    P v ->
    load_word dmem addr P.
  Proof. intros; eapply load_word_step; eauto. Qed.

  Definition start_state (dmem : mem) : otbn_state :=
    otbn_busy (0%nat, 0%nat) map.empty map.empty map.empty dmem [] [].
End Helpers.

Ltac solve_is_word_aligned t :=
  lazymatch goal with
  | H : is_word_aligned ?width ?a = true |- is_word_aligned ?width ?a = true => exact H
  | |- is_word_aligned _ (word.of_Z 0) = true => apply is_word_aligned_0; t
  | |- is_word_aligned _ (word.of_Z _) = true => apply is_word_aligned_imm; t
  | |- is_word_aligned ?width (word.add ?a ?offset) = true =>
      apply is_word_aligned_add; solve_is_word_aligned t
  | _ => t
  end.

Ltac simplify_side_condition_step :=
  match goal with
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- context [word.add ?a (word.of_Z 0)] => rewrite (word.add_0_r a)
  | |- context [if is_valid_addi_imm ?v then _ else _] =>
        replace (is_valid_addi_imm v) with true by (cbv [is_valid_addi_imm]; lia)
  | |- context [if is_valid_bn_imm ?v then _ else _] =>
        replace (is_valid_bn_imm v) with true by (cbv [is_valid_bn_imm]; lia)
  | |- context [if is_valid_mem_offset ?v then _ else _] =>
        replace (is_valid_mem_offset v) with true by (cbv [is_valid_mem_offset]; cbn; lia)
  | |- context [if is_valid_wide_mem_offset ?v then _ else _] =>
        replace (is_valid_wide_mem_offset v) with true by (cbv [is_valid_wide_mem_offset]; cbn; lia)
  | |- context [if is_word_aligned ?width ?a then _ else _] =>
        replace (is_word_aligned width a) with true by (symmetry; solve_is_word_aligned ltac:(lia))
  | |- context [if is_valid_shift_imm ?s then _ else _] =>
        replace (is_valid_shift_imm s) with true by (cbv [is_valid_shift_imm]; lia)
  | |- context [(_ + 0)%nat] => rewrite Nat.add_0_r
  | |- context [fetch_fn (?s, _, _) (?s, _)] => rewrite fetch_fn_name by auto
  | |- match fetch_fn ?fn ?pc with _ => _ end = Some _ => reflexivity
  | |- context [fetch_fn _ _] =>
      erewrite fetch_fn_sym by
      (cbn [fst snd]; first [ congruence | solve_map ])        
  | H : sep (ptsto ?addr _) _ ?m |- map.get ?m ?addr = Some _ =>
      eapply get_sep; solve [apply H]
  | |- map.get _ _ = Some _ => solve_map
  | H : map.get ?m ?k = Some _ |- context [match map.get ?m ?k with _ => _ end] =>
      rewrite H
  | |- context [match map.get _ _ with _ => _ end] => solve_map
  | |- context [advance_pc (?dst, ?off)] =>
      change (advance_pc (dst, off)) with (dst, S off)
| |- @store_word _ _ _ _ 32 _ _ _ _ _ =>
    eapply store_word32_step; [ assumption | lia | eassumption | ]
| |- @load_word _ _ _ _ 32 _ _ _ _ =>
    eapply load_word32_step; [ assumption | lia | eassumption | ]
| |- @store_word _ _ _ _ 256 _ _ _ _ _ =>
    eapply store_word256_step; [ assumption | lia | eassumption | ]
| |- @load_word _ _ _ _ 256 _ _ _ _ =>
    eapply load_word256_step; [ assumption | lia | eassumption | ]
  | |- (_ < _) => lia
  | |- (_ <= _) => lia                                   
  | |- (_ < _)%nat => lia
  | |- (_ <= _)%nat => lia
  | |- Some _ = Some _ => reflexivity
  | _ => first [ progress
                   cbn [run1 strt1 read_gpr write_gpr ctrl1
                          read_gpr_from_state
                          read_wdr write_wdr read_flag write_flag
                          set_pc update_state call_stack_pop call_stack_push
                          length hd_error tl skipn nth_error fold_left
                          fetch fetch_ctx Nat.add fst snd
                          err random option_bind proof_semantics
                          repeat_advance_pc advance_pc]
               | progress cbv [gpr_has_value]
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
  let wregs := lazymatch goal with
              | |- context [otbn_busy _ _ ?wregs] => wregs end in
  let flags := lazymatch goal with
              | |- context [otbn_busy _ _ _ ?flags] => flags end in
  let regs' := fresh "regs" in
  let wregs' := fresh "wregs" in
  let flags' := fresh "flags" in
  let Hr := fresh in
  remember regs as regs' eqn:Hr;
  assert (clobbers [] regs regs')
    by (cbv [clobbers]; subst regs'; right; reflexivity);
  let Hw := fresh in
  remember wregs as wregs' eqn:Hw;
  assert (clobbers [] wregs wregs')
    by (cbv [clobbers]; subst wregs'; right; reflexivity);
  let Hf := fresh in
  remember flags as flags' eqn:Hf;
  assert (clobbers [] flags flags')
    by (cbv [clobbers]; subst flags'; right; reflexivity);
  rewrite Hr, Hw, Hf;
  (* rewrite back in postcondition but not state *)
  lazymatch goal with
  | |- context [otbn_busy ?pc regs wregs flags] =>
      replace (otbn_busy pc regs wregs flags) with (otbn_busy pc regs' wregs' flags')
      by (rewrite Hr, Hw, Hf; reflexivity)
  end;
  clear Hr Hw Hf.

Ltac update_clobbers k l v H :=  
  let H' := fresh in
  pose proof (clobbers_step_if l k v _ _ H) as H';
  cbn [existsb orb gpr_eqb csr_eqb reg_eqb wdr_eqb wsr_eqb wreg_eqb flag_group_eqb FG0 FG1 flag_eqb] in H'.
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

Ltac find_innermost_put e :=
  lazymatch e with
  | map.put (map.put ?m ?k1 ?v1) ?k2 ?v2 =>
      find_innermost_put (map.put m k1 v1)
  | map.put ?m ?k ?v => e
  end.

Ltac update_tracking m1 m0 k v :=
  let T := lazymatch type of m0 with @map.rep ?T _ _ => T end in
  lazymatch find_innermost_put (map.put m0 k v) with
  | map.put ?m0 ?k ?v =>
      lazymatch goal with
      | H : @clobbers T _ _ ?l ?m ?m0 |- _ =>
          let v' := fresh "v" in
          set (v':= v);
          update_clobbers k l v' H;
          update_live_registers m0 k v' m1;
          clear H m0
      | _ => fail "Could not find hypothesis for clobbered values of type" T
      end
  end.
           
Ltac track_registers_update_step :=
  lazymatch goal with
  | |- context [otbn_busy _ (map.put ?regs0 ?k ?v)] =>
      let regs1 := fresh "regs" in
      update_tracking regs1 regs0 k v
  | |- context [otbn_busy _ _ (map.put ?wregs0 ?k ?v)] =>
      let wregs1 := fresh "wregs" in
      update_tracking wregs1 wregs0 k v
  | |- context [otbn_busy _ _ _ (map.put ?flags0 ?k ?v)] =>
      let flags1 := fresh "flags" in
      update_tracking flags1 flags0 k v
  | _ => idtac (* nothing was updated *)
  end.
Ltac track_registers_update :=
  track_registers_update_step; repeat progress track_registers_update_step.

Ltac infer_eqb_for_type T :=
  let eqb_spec := constr:(_:forall x y : T, BoolSpec (x = y) (x <> y) (_ x y)) in
  let eqb := lazymatch type of eqb_spec with Decidable.EqDecider ?f => f end in
  eqb.
Ltac combine_clobbers m2 :=
  lazymatch goal with
  | H0 : clobbers ?l0 ?m0 ?m1, H1 : clobbers ?l1 ?m1 m2 |- _ =>
      repeat lazymatch goal with
        | H : map.get m1 ?r = _ |- _ =>
            try (let Hnin := fresh in
                 assert (~ In r l1) as Hnin by (cbv [In]; intuition congruence);
                 pose proof (clobbers_not_in l1 _ _ _ _ H1 H Hnin);
                 clear Hnin);
            clear H
        end;
      let T := lazymatch type of l0 with list ?T => T end in
      let eqb := infer_eqb_for_type T in
      let l2 := (eval vm_compute in (List.dedup eqb (l0 ++ l1))) in
      pose proof (clobbers_trans_dedup (key_eqb:=eqb)
                    _ _ l2 _ _ _ H0 H1 ltac:(reflexivity));
      clear H0 H1; try clear m1
  | _ => idtac
  end.

(* use after a jump to combine the postconditions *)
Ltac track_registers_combine :=
  lazymatch goal with
  | |- context [otbn_busy _ ?regs ?wregs ?flags] =>
      combine_clobbers regs;
      combine_clobbers wregs;
      combine_clobbers flags
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
  Context {mem : map.map word32 byte} {mem_ok : map.ok mem}.
  Add Ring wring32: (@word.ring_theory 32 word32 word32_ok).
  Add Ring wring256: (@word.ring_theory 256 word256 word256_ok).
  
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
  Definition add_fn : otbn_function :=
    ("add"%string,
      map.empty,
      [(Add x5 x2 x3 : insn);
       (Ret : insn)]).
  Definition start_fn : otbn_function :=
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
  Definition mul_fn : otbn_function :=
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

  (* Test program : add two values from memory using pointers

     add_mem:
       lw   x2, 0(x12)
       lw   x3, 0(x13)
       add  x5, x2, x3
       sw   x5, 0(x12)
       ret
   *)
  Definition add_mem_fn : otbn_function :=
    ("add_mem",
      map.empty,
      [ (Lw x2 x12 0 : insn);
        (Lw x3 x13 0 : insn);
        (Add x5 x2 x3 : insn);
        (Sw x12 x5 0 : insn) ;
        (Ret : insn)])%string.


  (* Test program: add two bignums

     bignum_add:
       bn.add w5, w2, w3
       ret
  *)
  Definition bignum_add_fn : otbn_function :=
    ("bignum_add"%string,
      map.empty,
      [(Bn_add w5 w2 w3 0 FG0: insn);
       (Ret : insn)]).

  
  (* Test program : multiply small number by big number

     bignum_mul:
       bn.xor w2, w2, w2
       beq    x4, x0, _bignum_mul_end
       loop   x4, 2
         jal      x1, bignum_add
         bn.addi  w2, w5, 0
       _bignum_mul_end:
       ret
   *)
  Definition bignum_mul_fn : otbn_function :=
    Eval cbn [List.app length] in (
        let syms := map.empty in
        let body : list insn :=
          [ (Bn_xor w2 w2 w2 0 FG0 : insn);
            (Beq x4 x0 "_bignum_mul_end" : insn);
            (Loop x4 : insn);
            (Jal x1 "bignum_add" : insn);
            (Bn_addi w2 w5 0 FG0 : insn);
            (LoopEnd : insn)] in
        let syms := map.put syms "_bignum_mul_end" (length body) in
        let body := (body ++  [(Ret : insn)])%list in
        ("bignum_mul", syms, body))%string.

  (* Test program : add two bignums from memory using pointers

     bignum_add_mem:
       li       x2, 2
       li       x3, 3
       bn.lid   x2, 0(x12)
       bn.lid   x3, 0(x13)
       bn,add   w2, w2, w3
       bn.sid   x2, 0(x12)
       ret
   *)
  Definition bignum_add_mem_fn : otbn_function :=
    ("bignum_add_mem",
      map.empty,
      [ (Addi x2 x0 2 : insn);
        (Addi x3 x0 3 : insn);
        (Bn_lid x2 false x12 false  0 : insn);
        (Bn_lid x3 false x13 false  0 : insn);
        (Bn_add w2 w2 w3 0 FG0 : insn);
        (Bn_sid x2 false x12 false  0 : insn);
        (Ret : insn)])%string.

  Compute (link [mul_fn; add_fn]).
  Definition prog0 : program := ltac:(link_program [start_fn; add_fn]).

  Lemma prog0_correct v dmem R :
    (word32_at (word.of_Z 0) v * R)%sep dmem ->
    eventually
      (run1 (fetch:=fetch prog0))
      (fun st =>
         match st with
         | otbn_done _ dmem =>
             (word32_at (word.of_Z 0) (word.of_Z 5) * R)%sep dmem
         | _ => False
         end)
      (start_state dmem).
  Proof.
    cbv [prog0 start_state]; intros.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply store_word_step.
    { apply is_word_aligned_0. lia. }
    { rewrite word.unsigned_of_Z_0. vm_compute; reflexivity. }
    { use_sep_assumption. ecancel. }
    intros.
    eapply eventually_step_cps.
    simplify_side_condition.
    eapply eventually_done.
    cbv [addi_spec] in *. repeat destruct_one_match_hyp; try lia; [ ].
    rewrite !word.add_0_l in *.
    lazymatch goal with
    | H : (word_at ?p ?x * ?R)%sep ?m |- (word_at ?p ?y * ?R)%sep ?m =>
        replace y with x; [ apply H | ]
    end.
    apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
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
           /\ dmem' = dmem
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
           /\ clobbers [gpreg x5] regs regs').
  Proof.
    cbv [add_fn returns]. intros; subst.
    track_registers_init.
    
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | | | ].
    { solve_map. }
    { assumption. }
    { assumption. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
  Qed.

  Lemma add_mem_correct :
    forall regs wregs flags dmem cstack lstack a b pa pb Ra Rb,
      is_word_aligned 32 pa = true ->
      is_word_aligned 32 pb = true ->
      word.unsigned pa + 4 < DMEM_BYTES ->
      word.unsigned pb + 4 < DMEM_BYTES ->
      map.get regs (gpreg x12) = Some pa ->
      map.get regs (gpreg x13) = Some pb ->
      (* note: the separation-logic setup does not require the operands to be disjoint *)
      (word32_at pa a * Ra)%sep dmem ->
      (word32_at pb b * Rb)%sep dmem ->
      returns
        (fetch:=fetch_ctx [add_mem_fn])
        "add_mem"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           (word32_at pa (word.add a b) * Ra)%sep dmem'
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x3; gpreg x5] regs regs').
  Proof.
    cbv [add_mem_fn returns]. intros; subst.
    track_registers_init.
 
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
    eapply eventually_step_cps.
    simplify_side_condition.
    intros; subst.
    track_registers_update.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | | | ].
    { eauto using sep_put. }
    { assumption. }
    { assumption. }
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
           /\ dmem' = dmem
           /\ clobbers [] wregs wregs'
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
      ssplit; try reflexivity; [ | | ].
      { (* result value *)
        solve_map; subst_lets. cbv [addi_spec].
        destruct_one_match; try lia; [ ].
        apply f_equal. ring. }
      { assumption. }
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
           /\ dmem' = dmem
           /\ clobbers [] flags flags'
           /\ clobbers [] wregs wregs'
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
        simplify_side_condition. subst_lets; zsimplify.
        cbv [addi_spec]. destruct_one_match; try lia.
        apply f_equal.
        replace (word.of_Z (Z.of_nat (S (S i))))
          with (word.add (word:=word32) (word.of_Z (Z.of_nat (S i))) (word.of_Z 1));
          [ ring | ].
        apply word.unsigned_inj.
        rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap, word.unsigned_of_Z by lia.
        rewrite Z.add_1_r, <-Nat2Z.inj_succ. reflexivity. } }
 
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

  Lemma bignum_add_correct :
    forall regs wregs flags dmem cstack lstack a b,
      map.get wregs (wdreg w2) = Some a ->
      map.get wregs (wdreg w3) = Some b ->
      returns
        (fetch:=fetch_ctx [bignum_add_fn])
        "bignum_add"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w5) = Some (word.add a b)
           /\ map.get flags' (flagC FG0) = Some ((word.unsigned a + word.unsigned b) >? 2^256)
           /\ dmem' = dmem
           /\ clobbers [flagC FG0; flagM FG0; flagZ FG0; flagL FG0] flags flags'
           /\ clobbers [wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [add_fn returns]. intros; subst.
    track_registers_init.
    
    eapply eventually_step.
    { simplify_side_condition.
      apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | | | | ].
    { solve_map. }
    { solve_map. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
  Qed.

  Lemma word_xor_same {width : Z} {word : word width} {word_ok : word.ok word} :
    forall x : word, word.xor x x = word.of_Z 0.
  Proof.
    intros. apply word.unsigned_inj.
    rewrite word.unsigned_xor, word.unsigned_of_Z_0.
    rewrite Z.lxor_nilpotent. pose proof word.modulus_pos.
    apply Z.mod_0_l. lia.
  Qed.

  Lemma bignum_mul_correct :
    forall regs wregs flags dmem cstack lstack (a v : word256) (b: word32),
      map.get wregs (wdreg w2) = Some v -> (* ignored, xored *)
      map.get wregs (wdreg w3) = Some a ->
      map.get regs (gpreg x4) = Some b ->
      (length cstack < 8)%nat ->
      (length lstack < 8)%nat ->
      returns
        (fetch:=fetch_ctx [bignum_mul_fn; bignum_add_fn])
        "bignum_mul"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           map.get wregs' (wdreg w2) = Some (word.mul a (word.of_Z (word.unsigned b)))
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
  Proof.
    cbv [bignum_mul_fn returns]. intros; subst.
    repeat straightline_step.
 
    (* branch; use branch helper lemma *)
    eapply eventually_beq.
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { simplify_side_condition; reflexivity. }
    { (* case: b = 0, exit early *)
      intros; subst. eapply eventually_ret; [ reflexivity | eassumption | ].
      rewrite word.unsigned_of_Z_0. rewrite word.mul_0_r.
      ssplit; try reflexivity; [ | | ].
      { (* result value *)
        solve_map; subst_lets.
        rewrite word_xor_same. reflexivity. }
      { eapply clobbers_incl; eauto.
        cbv [incl In]; tauto. }
      { assumption. } }
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
           map.get wregs' (wdreg w2) = Some (word.mul a (word.sub (word.of_Z (word.unsigned b)) (word.of_Z (Z.of_nat i))))
           /\ map.get wregs' (wdreg w3) = Some a
           /\ map.get regs' (gpreg x4) = Some b
           /\ dmem' = dmem
           /\ clobbers [wdreg w2; wdreg w5] wregs wregs'
           /\ clobbers [] regs regs').
    { reflexivity. }
    { reflexivity. }
    { simplify_side_condition; reflexivity. }
    { apply Z2Nat.id; lia. }
    { lia. }
    { lia. }
    { (* prove invariant holds at start *)
      ssplit; simplify_side_condition; zsimplify; try reflexivity.
      { (* accumulator value *)
        subst_lets. apply f_equal. rewrite word_xor_same.
        ring. }
      { (* clobbered registers *)
        eapply clobbers_incl; eauto. cbv [incl In]; tauto. } }
    { (* invariant step; proceed through loop and prove invariant still holds *)
      intros; subst. repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.

      (* helper assertion that mul and add don't share symbols *)
      assert (function_symbols_disjoint bignum_add_fn bignum_mul_fn).
      { cbv [function_symbols_disjoint]; cbn [bignum_add_fn bignum_mul_fn fst snd].
        ssplit; solve_map; try congruence; [ ].
        cbv [map.disjoint]; intros *. rewrite map.get_empty; congruence. }

      (* jump to "bignum_add" function *)
      eapply eventually_jump.
      { reflexivity. }
      { lia. }
      { apply bignum_add_correct; eauto. }
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
        apply f_equal. ring. }
      { (* case: 0 < i, loop continues *)
        intros; subst. eapply eventually_done.
        left. do 4 eexists; ssplit; [ .. | reflexivity ]; solve_map; [ ].
        simplify_side_condition. subst_lets; zsimplify.
        apply f_equal.
        replace (word.of_Z (width:=256) (Z.of_nat (S (S i))))
          with (word.add (width:=256) (word.of_Z (Z.of_nat (S i))) (word.of_Z 1));
          [ ring | ].
        apply word.unsigned_inj.
        rewrite !word.unsigned_add, !word.unsigned_of_Z_nowrap by lia.
        cbv [word.wrap]. rewrite Z.mod_small by lia. lia. } }
 
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

  Check map.of_list_word_at.
  Print wide_word_load.  
  Lemma bignum_add_mem_correct :
    forall regs wregs flags dmem cstack lstack a b pa pb Ra Rb,
      is_valid_wide_addr pa = true ->
      is_valid_wide_addr pb = true ->
      map.get regs (gpreg x12) = Some pa ->
      map.get regs (gpreg x13) = Some pb ->
      (* note: the separation-logic setup does not require the operands to be disjoint *)
      (ptsto pa a * Ra)%sep dmem ->
      (ptsto pb b * Rb)%sep dmem ->
      returns
        (fetch:=fetch_ctx [bignum_add_mem_fn])
        "bignum_add_mem"%string regs wregs flags dmem cstack lstack
        (fun regs' wregs' flags' dmem' =>
           (ptsto pa (word.add a b) * Ra)%sep dmem'
           /\ clobbers [flagM FG0; flagL FG0; flagZ FG0; flagC FG0] flags flags'
           /\ clobbers [wdreg w2; wdreg w3] wregs wregs'
           /\ clobbers [gpreg x2; gpreg x3] regs regs').
  Proof.
    cbv [bignum_add_mem_fn returns]. intros; subst.
    track_registers_init.
    
    eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_step.
    { simplify_side_condition.
      
      
      apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_step.
    { simplify_side_condition. apply eq_refl. }
    intros; subst.
    track_registers_update.
    eapply eventually_ret; [ reflexivity | eassumption | ].
    ssplit; try reflexivity; [ | | | ].
    { eauto using sep_put. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
    { eapply map.only_differ_subset; [ | eassumption ].
      cbv. tauto. }
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
  Definition repeat_add (n : nat) : otbn_function :=
    (("add" ++ String.of_nat n)%string,
      map.empty,
      (Addi x2 x0 0 : insn) :: repeat (Add x2 x2 x3 : insn) n ++ [(Ret : insn)]).
  Definition add100_fn : otbn_function := Eval vm_compute in (repeat_add 100).

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
           /\ dmem' = dmem
           /\ clobbers [] wregs wregs'
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
    ssplit; try reflexivity; [ | | ].
    { solve_map. apply (f_equal Some).
      repeat (apply mul_by_add_step; [ lia | ];
              cbn [Z.sub Z.add Z.opp Z.pos_sub Pos.pred_double]).
      lazymatch goal with |- ?x = word.mul _ (word.of_Z 0) => subst x end.
      cbv [addi_spec]. destruct_one_match; try lia; [ ].
      ring. }
    { eassumption. }
    { (* only_differ clause *)
      eapply clobbers_incl; eauto. cbv [incl In]. tauto. }
  Time Qed. (* 0.75s *)
End __.
End Test.

(* Next: prove fold_bignum, RSA trial div *)
(* Next: add mulqacc *)
(* Next: prove sha512 copy *)
(* Next: try to add more realistic error conditions for e.g. loop errors *)
(* Next: add notations back *)
(* Next: provable multiplication blocks *)
(* Next: add more insns needed for 25519 mul *)
(* Next: prove 25519 mul *)
(* Next: prove bignum op with var #regs (e.g. mul) *)
