From mathcomp Require Import ssreflect fingroup.
Require Import Assumption.

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

Section QuantumlibExtra.

From QuantumLib Require Import Quantum.

Lemma C1_neq_mC1: C1 <> -C1.
Proof.
  move => F.
  inversion F.
  assert (H: 1 <> (-1)%R) by lra.
  apply (H H0).
Qed.


Lemma state_linear n:
  forall (a b: Vector n), a = b -> a .+ -C1 .* b = Zero.
Proof.
  move => a b ->.
  lma.
Qed.

Lemma zero_state_sufficient n:
  forall (a: Vector n) (c: C), 
    c .* a = Zero -> c <> C0 -> a = Zero.
Proof.
  move => a c Hac0 Hc0.
  assert (c .* a = c .* Zero). {
    rewrite Hac0.
    lma.
  }
  apply Mscale_div in H; auto.
Qed.

Lemma negate_change_state n:
  forall (ψ:  Vector n), ψ <> Zero -> -C1 .* ψ <> ψ.
Proof.
  move => psi Hnz Heq.
  apply state_linear in Heq.
  rewrite -Mscale_plus_distr_l in Heq. 
  apply zero_state_sufficient in Heq.
  apply Hnz.
  apply Heq.
  move => H.
  inversion H.
  assert ((- (1) + - (1))%R <> 0) by lra.
  apply H0.
  apply H1.
Qed. 



End QuantumlibExtra.