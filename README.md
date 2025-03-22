# OTBN Formal Model

This is an experimental formalization of OTBN semantics in Rocq.
It makes use of omnisemantics and separation logic to drive proofs.

The model is based on some earlier experiments that verified [P256](https://gist.github.com/jadephilipoom/5c1910fd355f730238c99ce620aed98a) and [25519](https://gist.github.com/jadephilipoom/41bb78778ddffdcd3f9e17ae5be26c73) modular multiplication algorithms against standalone, ad-hoc models of OTBN.
Those models included only the functionality and instructions needed for the specific proofs.
