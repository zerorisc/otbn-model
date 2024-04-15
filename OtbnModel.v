Require Import Coq.Strings.String.
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

  (*
  (* Program graph with control flow. Block constructors are named
     after the control-flow instruction they end with. *)
  Inductive Block : Type :=
  | Ret : list Insn -> Block
  | Ecall : list Insn -> Block
  (* Tail-call pattern: jal x0, foo *)
  | JumpNoLink : list Insn -> string -> Block
  (* Function call pattern: jal x1, foo *)
  | Call : list Insn -> string -> Block -> Block
  | Bne : list Insn -> gpr -> gpr -> string -> Block -> Block
  | LoopEnd : list Insn -> Block (* loop start *) -> Block (* post-loop *) -> Block
  .

  Notation "x ;; 'ecall'" := (Ecall x) (at level 40).
  Notation "x ;; 'ret'" := (Ret x) (at level 40).
  Notation "x ;; 'jal' 'x1' , foo ;; y" := (Call x foo y) (at level 60).
  Notation "x ;; 'jal' 'x0' , foo" := (JumpNoLink x foo) (at level 40).
  Notation "x ;; 'bne' a , b , foo ;; y" := (Bne x a b foo y) (at level 60).

  (* Test notations. *)
  Check (bn.add w1, w2, w3 << 0, FG0).
  Check (bn.add w1, w2, w3 >> 3, FG0).
  Check ([bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; ecall).
  Check ([bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; jal x1, "foo" ;; [] ;; ret).
  Check ([bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; jal x0, "foo").
  Check ([bn.add w1, w2, w3 >> 3, FG0; bn.addm w3, w3, w3] ;; bne x1, x2, "foo" ;; [] ;; ret).
   *)
End Notations.

(* error monad : either a value or an error message *)
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
Definition assertion (cond : bool) (msg : string) : maybe unit :=
  if cond then inl tt else inr msg.
Local Notation "a <- b ; c" := (bind b (fun a => c)) (at level 100, right associativity).
Local Notation "'assert!' x msg" := (if x then inr msg%string else inl tt) (at level 40).
Local Notation Ok := inl (only parsing).
Local Notation Err := inr (only parsing).

(* bitwise operation shorthand *)
Local Infix "|'" := Z.lor (at level 40, only parsing) : Z_scope.
Local Infix "&'" := Z.land (at level 40, only parsing) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 40, only parsing) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 40, only parsing) : Z_scope.
Local Coercion Z.b2z : bool >-> Z.

(* Executable model of OTBN. *)
Section Exec.
  (* Parameterize over randomness implementation. *)
  Context {rnd : nat -> Z} {rnd_range : forall x, 0 <= rnd x < 2^256}.
  Context {urnd : nat -> Z} {urnd_range : forall x, 0 <= urnd x < 2^256}.

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
      (* Data memory *)
      dmem : map Z Z;
      (* Call stack. *)
      callstack : list Z;
      (* Loop stack; holds the number of iterations remaining for each loop. *)
      loopstack : list Z;
      (* Instruction counter. *)
      insn_counter : nat;
    }.

  Definition read_gpr (st : OtbnState) (r : gpr) : maybe Z :=
    match r with
    | x0 => Ok 0 (* x0 always reads as 0 *)
    | x1 =>
        (* TODO: a direct read from the call stack is possible but
           rare in practice. For now, don't model it. *)
        Err "Attempt to directly read from the call stack. This behavior is not yet modelled."%string
    | _ => map_err (mget st.(regfile) (gpreg r)) "GPR undefined"
    end.

  Definition read_wdr (st : OtbnState) (r : wdr) : maybe Z :=
    map_err (mget st.(regfile) (wdreg r)) "WDR undefined".

  Definition read_wsr (st : OtbnState) (r : wsr) : maybe Z :=
    match r with
    | RND => Ok (rnd (st.(insn_counter)))
    | URND => Ok (urnd st.(insn_counter))
    | _ => map_err (mget st.(regfile) (wsreg r)) "WSR undefined"
    end.

  Definition read_flag (st : OtbnState) (f : flag) : maybe bool :=
    map_err (mget st.(flagfile) f) "Flag undefined".

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
    {| regfile := st.(regfile);
      flagfile := st.(flagfile);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter) + 1;
    |}.

  Definition regfile_set (st : OtbnState) (r : reg) (v : Z) : OtbnState :=
    {| regfile := mset st.(regfile) r v;
      flagfile := st.(flagfile);
      dmem := st.(dmem);
      callstack := st.(callstack);
      loopstack := st.(loopstack);
      insn_counter := st.(insn_counter);
    |}.

  Definition cast32 (v : Z) : Z := v &' Z.ones 32.
  Definition cast256 (v : Z) : Z := v &' Z.ones 256.

  Definition write_gpr (st : OtbnState) (r : gpr) (v : Z) : maybe OtbnState :=
    match r with
    | x0 => Ok st
    | x1 =>
        (* TODO: this should push to the call stack, but is
           practically never used. For now, don't model this behavior
           and treat it as an error. *)
        Err "Attempt to write to call stack. This behavior is not yet modelled."%string
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
    ((s =? 0)%Z || (s =? 64)%Z || (s =? 128%Z) || (s =? 192%Z))%bool.
  (* other shift immediates must be multiples of 8 and in the range [0,248] *)
  Definition valid_arith_shift (s : shift) : bool :=
    let s := match s with
             | lshift x => x
             | rshift x => x
             end in
    ((s mod 8 =? 0)%Z && (0 <=? s)%Z && (s <=? 248)%Z)%bool.

  Definition addm_spec (x y m : Z) : Z :=
    let r := x + y in
    if r >? m then r - m else r.
  Definition subm_spec (x y m : Z) : Z :=
    let r := x - y in
    if r <? 0 then r + m else r.

  Definition exec1
    (st : OtbnState) (i : Insn) : maybe OtbnState :=
    match i with
    | Mulqacc z x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc" ;
         x <- read_limb st x ;
         y <- read_limb st y ;
         acc <- read_wsr st ACC ;
         Ok (write_wsr st ACC (acc + (x * y) << s)))
    | Mulqacc_wo z d x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc.wo" ;
         x <- read_limb st x ;
         y <- read_limb st y ;
         acc <- read_wsr st ACC ;
         let acc' := acc + ((x * y) << s) in
         Ok (write_wdr (write_wsr st ACC acc') d acc'))
    | Mulqacc_so z L d x y s =>
        let st := if z then write_wsr st ACC 0 else st in
        (_ <- assertion (valid_mul_shift s) "Invalid shift for bn.mulqacc.so" ;
         x <- read_limb st x ;
         y <- read_limb st y ;
         old <- read_wdr st d ;
         acc <- read_wsr st ACC ;
         let acc' := acc + ((x * y) << s) in
         let accL := acc' &' (Z.ones 128) in
         let accH := acc' >> 128 in
         let dL := old &' (Z.ones 128) in
         let dH := old >> 128 in
         let d' := if L
                   then (accL |' (dH << 128))
                   else (dL |' (accL << 128)) in
         Ok (write_wdr (write_wsr st ACC acc') d d'))
    | Addm d x y =>
         (x <- read_wdr st x ;
          y <- read_wdr st y ;
          m <- read_wsr st MOD ;          
          Ok (write_wdr st d (addm_spec x y m)))
    | Subm d x y =>
         (x <- read_wdr st x ;
          y <- read_wdr st y ;
          m <- read_wsr st MOD ;          
          Ok (write_wdr st d (subm_spec x y m)))
    | Add d x y s fg =>
        (_ <- assertion (valid_arith_shift s) "Invalid shift for bn.add" ;
         c <- read_flag st (flagC fg) ;
         x <- read_wdr st x ;
         y <- read_wdr st y ;
         Ok (write_wdr st d (x + y + c)))
    | _ => Err "NotImplemented"%string
    end.

  Definition exec_straightline
    (st : OtbnState) (insns : list Insn) : maybe OtbnState :=
    fold_left (fun st i => (st <- st;
                            st <- exec1 st i;
                            Ok (inc_insn_counter st))) insns (Ok st).    

  Print Block.
  Fixpoint exec
    (labels : map string Block) (st : OtbnState) (start : Block) : maybe OtbnState :=
    match start with
    | Ret insns =>
        (st <- exec_straightline st insns ;
         loc <- map_err (hd_error st.(callstack)) "Call stack empty"%string ;
         exec labels st loc)
    | _ => Err "NotImplemented"%string
    end.

  

  
End Exec.
