From mathcomp Require Import ssreflect fingroup.

Section commutative.

Definition commute_at {T: Type} (op: T -> T -> T) (a b: T) : Prop :=
  op a b = op b a.

Definition anticommute_at {T: Type} (op: T -> T -> T) (opp: T -> T) (a b: T) : Prop :=
  op a b = opp (op b a).
  
Definition commute {T: Type} (op: T -> T -> T) : Prop :=
  forall a b: T, commute_at op a b.

Definition anticommute {T: Type} 
  (op: T -> T -> T) (opp: T -> T) : Prop :=
forall a b: T, anticommute_at op opp a b.

Definition bicommute {T: Type}
  (op: T -> T -> T) (opp: T -> T) : Prop :=
forall a b: T, commute_at op a b \/ anticommute_at op opp a b.


Locate commute.

(* When it is mathcomp group, we can simplify the definition *)
Definition commuteg (T: finGroupType) :=
  forall (x y: T), fingroup.commute x y.

(* TODO: Define anitcommute with abelian monoid *)

End commutative.

From QuantumLib Require Import Quantum.

Lemma C1_neq_mC1: C1 <> -C1.
Proof.
  move => F.
  inversion F.
  assert (H: 1 <> (-1)%R) by lra.
  apply (H H0).
Qed.
