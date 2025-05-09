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

Require Import Reals.
Require Import DiscrR.
Require Import Lra.
Open Scope R_scope.

Section RealExtra.

Lemma l1:
1 <> 0. Proof. by discrR. Qed.

Lemma r_sqrt_1_spec:
  forall (r: R),
  r^2 = 1 -> r = 1 \/ r = -1.
Proof.
  intros r H.
  move: (Rsqr_sol_eq_0_0 (mknonzeroreal 1 l1) 0 (-1) r).
  rewrite /sol_x1 /sol_x2 /Delta /Rsqr /Delta_is_pos /Delta //=.
  replace (0² - 4 * 1 * -1) with 4.
  replace ((- 0 + sqrt (0 * 0 - 4 * 1 * -1)) / (2 * 1)) with (1).
  replace ((- 0 - sqrt (0 * 0 - 4 * 1 * -1)) / (2 * 1)) with (-1).
  intros H0.
  assert (H1: 0 <= 4) by lra. 
  apply H0 in H1.
  apply H1. lra.
  replace (0 * 0 - 4 * 1 * -1) with 4 by lra.
  replace 4 with (2 ^ 2) by (simpl; lra).
  replace (sqrt (2 ^ 2)) with 2. lra.
  symmetry. apply (sqrt_pow2 2). lra.
  replace ((0 * 0 - 4 * 1 * -1)) with 4 by lra.
  replace 4 with (2 ^ 2) by (simpl; lra).
  replace (sqrt (2 ^ 2)) with 2. lra.
  symmetry. apply (sqrt_pow2 2). lra.
  rewrite Rsqr_0. lra.
Qed.

Lemma r_system_20:
  forall (r1 r2: R),
  (r1 * r1 - r2 * r2 = 1) ->
  (r1 * r2 + r2 * r1 = 0) ->
  (r1, r2) = (1, 0) \/ (r1, r2) = (-1, 0).
Proof.
  move => a b H0 H1.
  assert (a * b = 0).
  {
    rewrite Rmult_comm in H1. 
    rewrite Rplus_diag in H1.
    apply Rmult_integral in H1.
    destruct H1.
    - exfalso. contradict H. discrR.
    - rewrite Rmult_comm. by apply H.
  }
  apply Rmult_integral in H.
  destruct H.
  - exfalso. subst. 
    move: H0.
    rewrite Rmult_0_l Rminus_0_l.
    replace (b * b) with (b ^ 2) by lra.
    move => H.
    apply Ropp_eq_compat in H.
    rewrite Ropp_involutive in H.
    assert (b^2 + 1 <> 0). {
      apply Rplus_le_lt_0_neq_0.
      apply pow2_ge_0.
      lra.
    }
    apply H0.
    rewrite H. lra.
  - subst. move: H0.
    rewrite Rmult_0_r Rminus_0_r.
    replace (a * a) with (a ^ 2) by lra.
    move => H.
    move: (r_sqrt_1_spec a H) => H0.
    destruct H0.
    subst. by left.
    subst. by right.
Qed. 

Close Scope R_scope.
Open Scope C_scope.

End RealExtra.

From QuantumLib Require Import Quantum.

Section QuantumlibExtra.


Theorem c_sqrt_1_spec:
  forall (c: Complex.C),
  c ^ 2 = 1 -> c = 1 \/ c = -1.
Proof.
  move => [r1 r2].
  rewrite /C1 /RtoC.
  rewrite /RtoC //= Cmult_1_r /Cmult //= => H.
  apply pair_equal_spec in H.
  case H => H1 H2. clear H.
  by apply r_system_20.
Qed.

Lemma Msub_self {n m}:
  forall (A: Matrix n m),
  A .+ -1 .* A = Zero.
Proof. by move => A; lma. Qed.

Lemma C1_neq_mC1: C1 <> -C1.
Proof.
  move => F.
  inversion F.
  assert (H: 1 <> (-1)%R) by lra.
  apply (H H0).
Qed.

Lemma Cmult_neq:
  forall (a c1 c2: C),
  a <> 0 -> c1 <> c2 -> c1 * a <> c2 * a.
Proof. 
  move => a c1 c2 Anz H F.
  assert (HF: c1 = c2). {
    apply (Cmult_cancel_r a); auto.
  }
  apply H.
  apply HF.
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

Lemma Maccess_scale:
  forall {n m : nat} (A: Matrix n m) (c:C) (i j : nat),
  (c .* A) i j = c * (A i j).
Proof. by intros; lca. Qed.

Lemma Mscale_cancel:
  forall {n m : nat} (c1 c2 : C) (A: Matrix n m),
  WF_Matrix A ->
  A <> Zero ->  
  c1 .* A = c2 .* A -> c1 = c2.
Proof.
  move => n m c1 c2 A Hwf Hnz H.
  apply Mnonzero_spec in Hnz.
  destruct Hnz as [i [j Hnzs]].
  case (Ceq_dec c1 c2); auto => Hc.
  assert (Hright: (c1 .* A) i j = (c2 .* A) i j).
  {
    by rewrite H.
  }
  assert (Hleft: (c1 .* A) i j <> (c2 .* A) i j).
  {
    rewrite !Maccess_scale.
    apply Cmult_neq; auto.
    destruct Hnzs as [_ [_ Aijneq]].
    apply Aijneq.
  }
  contradict Hright.
  apply Hleft.
  apply Hwf.
Qed.  

Lemma Mscale_cancel_0 {n m}:
  forall (A: Matrix n m) (c: C),
  WF_Matrix A -> A <> Zero -> c .* A = Zero -> c = 0.
Proof.
  move => A C Hwf HAz.
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
  move: (involutary_matrix_spec A Hinv) => Aspec.
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
  apply c_sqrt_1_spec.
  apply Hwfa.
  apply HdetA.
Qed.

End QuantumlibExtra.