Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Separation.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import Otbn.Semantics.Semantics.
Import ListNotations.
Local Open Scope Z_scope.

(*** Defines generic bignums (arrays of wide words interpreted as integers). ***)

Section WithWord.
  Context {width} {word : word.word width}.

  (* Interpret a bignum as an unbounded integer. *)
  Definition eval (x : list word) : Z :=
    fold_right (fun xi acc => word.unsigned xi + 2^width*acc) 0 x.

  Section WithMem.
    Context {addr_width} {addr : word.word addr_width} {mem : map.map addr byte}.

    (* Separation-logic predicate for bignums. *)
    Definition bignum_at (ptr : addr) (v : list word) : mem -> Prop :=
      bytes_at ptr (le_split (Z.to_nat 32 * length v) (eval v)).
  End WithMem.
End WithWord.
