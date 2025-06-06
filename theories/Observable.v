(* 
This file describe pauli operator as quantum observale.
Important Definition:
- "'Meas P on psi --> m" := measuring P on state psi yields m
*)
From QuantumLib Require Import Quantum.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.
Require Import PauliGroup.
Require Import Action.
Require Import Stabilizer.
Require Import WellForm.
Require Import PauliProps.
Require Import ExtraSpecs.
Require Import Operations.
Open Scope form_scope.
Set Bullet Behavior "Strict Subproofs".

(* An operator is hermitian if it is self-adjoint   *)
Definition hermitian {n:nat} (H: Square (2^n)): Prop :=
  H† = H.

Notation is_observable := hermitian.

(* eigen_measure m M ψ captures the projective measurement postulate:
  if ψ is an eigenvector of Hermitian observable M with eigenvalue m, 
  then measuring M on ψ yields m with certainty (probability = 1). *)
Definition eigen_measure {n} (m: C) (M: Square (2^n)) (psi: Vector (2^n)) :=
  WF_Matrix M /\ hermitian M /\ M × psi = m .* psi.

(* because every pauli operator is hermitian, 
  they can all be viewed as observable *)
Notation PauliObservable := PauliString.
(* Notation Just for readability *)
Notation ErrorOperator := PauliOperator.

Lemma pauli_base_hermitian:
  forall (p: PauliBase),
  @hermitian 1%nat (int_p1b p).
Proof.
  move => p.
  rewrite /hermitian.
  case p; simpl.
  apply id_adjoint_eq.
  apply σx_hermitian.
  apply σy_hermitian.
  apply σz_hermitian.
Qed.

Fact pauli_hermitian {n} :
  forall (operator: PauliOperator n), hermitian (int_pnb operator).
Proof.
  rewrite /hermitian /int_pn /PauliObservable //= => pt.
  induction n.
  - by rewrite tuple0 /= id_adjoint_eq.
  - case: pt / tupleP => hx tx.
    rewrite /= theadCons .
    restore_dims.
    by rewrite kron_adjoint IHn pauli_base_hermitian.
Qed.

(* 
If a quantum state ψ is stabilized by a Pauli operator p (i.e., p ψ = ψ), 
then measuring the corresponding observable yields outcome 1 with certainty.
*)
Theorem stab_eigen_measure_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> eigen_measure 1 (int_pnb p) psi.
Proof.
  split => H.
  - rewrite /eigen_measure.
    split. apply int_pnb_wf.
    split. apply pauli_hermitian.
    apply PauliOperator_stab in H.
    rewrite H. by Qsimpl.
  - move: H. 
    rewrite /eigen_measure => [[_ [_ H]]].
    rewrite /stab /act_n /applyP /=. Qsimpl.
    rewrite H. by Qsimpl.
Qed.

(* 
  What we are really interesting is to use pauli operator
  as observables.
 *)
Definition eigen_measure_p {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :=
  (int_pnb P) × psi = m .* psi.
  
Theorem eigen_measure_p_correct {n}:
  forall (m:C) (P: PauliOperator n) (psi: Vector (2^n)),
  eigen_measure_p m P psi <-> eigen_measure m (int_pnb P) psi.
Proof.
  move => m P psi.
  rewrite /eigen_measure_p /eigen_measure.
  split.
  - move => H.
    split => //. apply int_pnb_wf.
    split => //. apply pauli_hermitian.
  - move => [_ [_ H]].
    exact H.
Qed. 

Lemma eigen_measure_p_applyP {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :
  eigen_measure_p m P psi <->
  applyP psi P = m .* psi.
Proof.
  rewrite /eigen_measure_p /applyP.
  by rewrite !/PauliOpToElem !int_pn_one.
Qed.



Corollary stab_eigen_measure_p_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> eigen_measure_p 1 p psi.
Proof.
  split => HH.
  - rewrite eigen_measure_p_correct.
    by apply stab_eigen_measure_1.
  - rewrite eigen_measure_p_correct in HH.
    by rewrite stab_eigen_measure_1.
Qed.

Notation "''Meas' P 'on' psi '-->' m " := (eigen_measure_p m P psi)
 (at level 8) : form_scope.

(* this line is required *)
Import all_pauligroup. 

Section Eigenvalue. 

Lemma operator_nonzero_det:
  forall (n:nat) (op: PauliOperator n),
  Determinant (int_pn op) <> 0.
Proof.
  move => n op.
  apply invertible_iff_det_neq_0.
  auto with wf_db.
  rewrite /invertible /PauliOpToElem.
  remember ((One, op): PauliElement n) as p.
  exists (int_pn (invg p)).
  split.
  auto with wf_db.
  rewrite /Minv !int_pn_Mmult.
  change mul_pn with (@mulg (PauliElement n)).
  rewrite mulgV mulVg /=.
  rewrite id_int_pnb. 
  by Qsimpl.
Qed.


(* Pauli operators has eivenvalue either 1 or -1 *)
Theorem operator_eigenvalue {n}:
  forall (op: PauliOperator n) (psi: Vector (2^n)) (lambda: C),
    psi <> Zero ->
    WF_Matrix psi ->
    applyP psi op = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Proof.
  move => op psi lambda Hnz Hpwf Happ.
  rewrite /applyP in Happ.
  remember (int_pn _) as m.
  apply (involutive_eigenvalue n (int_pn op) psi lambda); auto with wf_db.
  apply (operator_nonzero_det).
  subst.
  move: (pauli_involutive op).
  rewrite /mulg /= => H.
  Qsimpl.
  rewrite -int_pnb_Mmult H fold_rel_phase_involutive PauliProps.id_int_pnb //=. 
  by Qsimpl. subst. by [].
Qed.

End Eigenvalue.

Require Import ExtraSpecs.


(* A helper to let coq make type right *)

Definition t2o {n}: (n.-tuple PauliBase) -> PauliOperator n := Datatypes.id.


Lemma eigen_measure_p_unique {n}:
  forall (phi: Vector (2^n)) (ob: PauliObservable n)  (r q: C),
  WF_Matrix phi ->
  'Meas ob on phi --> r ->
  'Meas ob on phi --> q ->
  phi <> Zero -> 
  r = q.
Proof.
  move => phi ob r q Hwf.
  rewrite /eigen_measure_p => H1 H2 Hnt.
  have: (int_pnb ob × phi = int_pnb ob × phi) by auto.
  rewrite {1}H1 H2.
  apply Mscale_cancel; auto.
Qed.

Lemma int_pnb_concat {n m}:
  forall (op0: PauliString n) (op1: PauliString m) ,
  (int_pnb [tuple of op0 ++ op1]) = 
  (int_pnb op0) ⊗ (int_pnb op1).
Proof.
  simpl.
  move => p q.
  induction n.
  - rewrite tuple0.
    Qsimpl. 
    + by rewrite tupleE catNil. 
  - case: p / tupleP => hp tp.
    rewrite !tupleE !catCons.
    rewrite int_pnb_cons /= theadCons beheadCons IHn /=.
    rewrite /pow_add. 
    rewrite (kron_assoc (int_p1b hp ) (int_pnb tp) (int_pnb q)); auto with wf_db.
Qed. 

Lemma applyP_kron {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Apply t2o [tuple of op0 ++ op1] on (phi0 ⊗ phi1) ) = 
  ('Apply op0 on phi0) ⊗ ('Apply op1 on phi1).
Proof.
  move => op0 op1 phi0 phi1.
  rewrite /applyP /=. Qsimpl.
  rewrite /t2o /Datatypes.id.
  rewrite int_pnb_concat.
  rewrite kron_mixed_product'; try auto;
  by rewrite Nat.pow_add_r.
Qed.
(* A p = - p /\ B q = q -> (A ++ B) (q ⊗ p) = - (q ⊗ p) *)
Lemma eigen_measure_p_m1_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 --> (-1)) ->
  ('Meas op1 on phi1 -->  1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> (-1).
Proof.
  rewrite /eigen_measure_p.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite int_pnb_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1 Mscale_1_l Mscale_kron_dist_l.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma eigen_measure_p_1m_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  1) ->
  ('Meas op1 on phi1 --> -1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> (-1).
Proof.
  rewrite /eigen_measure_p.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite int_pnb_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma eigen_measure_p_11_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  1) ->
  ('Meas op1 on phi1 -->  1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> 1.
Proof.
  rewrite /eigen_measure_p.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite int_pnb_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma eigen_measure_p_mm_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  -1) ->
  ('Meas op1 on phi1 -->  -1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> 1.
Proof.
  rewrite /eigen_measure_p.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite int_pnb_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.
