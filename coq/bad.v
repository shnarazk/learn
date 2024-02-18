(* [global] *)
From Coq Require Import Relations.

Definition bad_theorem : Prop := forall (A: Type) (R : relation A),
  symmetric _ R -> transitive _ R -> reflexive _ R.

Theorem correct_version : ~ bad_theorem.
Proof.
  unfold bad_theorem.
  unfold symmetric.
  unfold transitive.
  unfold reflexive.
