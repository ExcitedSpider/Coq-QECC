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



Lemma Mscale_cancel_0 {n m}:
  forall (A: Matrix n m) (c: C),
  A <> Zero -> c .* A = Zero -> c = 0.
Proof.
  move => A C HAz.
  replace Zero with (0 .* A).
  by apply Mscale_cancel.
  by rewrite Mscale_0_l.
Qed.

(* If P^2 = I, all eigenvalues λ of P satisfy λ^2 = 1 *)
Lemma involutive_eigenvalue n:
  forall (A: Square (2^n)) (psi: Vector (2^n)) (lambda: C),
    psi <> Zero ->
    WF_Matrix A ->
    Determinant A <> 0 ->
    WF_Matrix psi ->
    A × A = I (2^n) ->
    A × psi = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Proof.
  move => A psi lambda Hnz Hwfa HdetA Hwfpsi Hinv Heigen.
  move: (involutoray_matrix_spec A Hinv) => Aspec.
  assert (
    Step1: Minverse A × (A × psi) = Minverse A × (lambda .* psi) 
  ). by rewrite Heigen.
  move: Step1.
  rewrite -!Mmult_assoc Mmult_Minverse_l.
  rewrite -Aspec Mscale_mult_dist_r Heigen => Hin.
  assert (Step2: psi = lambda^2 .* psi).
  {
    move: (Mmult_1_l _ _ _ Hwfpsi) => Hmult_1_l'.
    rewrite Hmult_1_l' in Hin.
    rewrite {1}Hin.
    rewrite Mscale_assoc.
    by rewrite /Cpow Cmult_1_r. 
  }
  assert (Step3: (lambda^2 - 1) .* psi = Zero). {
    rewrite -(Msub_self psi) {2}Step2.
    rewrite -Mscale_plus_distr_l.
    lma.
  }
  assert (Step4: (lambda ^ 2 - C1) = 0). {
    apply (Mscale_cancel_0 psi); auto.
  }
  assert (Step5: lambda ^2 - C1 + C1 = 0 + C1). {
    apply Cplus_simplify; auto.
  }
  move: Step5. 
  rewrite -Cplus_assoc.
  replace ((- C1 + C1)) with C0 by by lca.
  Csimpl.
  apply c_sqrt_1_sepcs.
  apply Hwfa.
  apply HdetA.
Qed.

End QuantumlibExtra.