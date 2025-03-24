# OTBN Formal Model

This is an experimental formalization of OTBN semantics in Rocq.
It makes use of [omnisemantics](https://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf) and separation logic to drive proofs.

The model is based on some earlier experiments that verified [P256](https://gist.github.com/jadephilipoom/5c1910fd355f730238c99ce620aed98a) and [25519](https://gist.github.com/jadephilipoom/41bb78778ddffdcd3f9e17ae5be26c73) modular multiplication algorithms against standalone, ad-hoc models of OTBN.
Those models included only the functionality and instructions needed for the specific proofs.

## Requirements and Quickstart

Clone the repo and run `make`.
Requires coqutil and Rocq/Coq (tested with version 8.19.0).

## Examples

You can find example programs and their proofs in the `Otbn/Examples/` directory.

## Core Model

The core model of OTBN is under `Otbn/ISA` and `Otbn/Semantics`.
The `ISA` folder defines the instructions, and `Semantics` describes what they do to OTBN's state.

The model can be instantiated in two ways.
When it's run on a program and start state, it can be set up to return either:
- a concrete final state when it's run on a program (executable semantics, represented by `exec1`)
- a statement that holds on the final state (`after1`)

This setup allows smooth reasoning about things like random numbers in proofs while preserving the ability to have a concrete executable model.

## Linker

`Otbn/Linker` contains a limited but functional linker for OTBN programs, and a proof of its correctness.
