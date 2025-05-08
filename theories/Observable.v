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
Require Import Assumption.
Require Import Stabilizer.
Require Import WellForm.
Require Import PauliProps.
Require Import ExtraSpecs.
Open Scope form_scope.
Set Bullet Behavior "Strict Subproofs".

(* An operator is hermitian if it is self-adjoint   *)
Definition hermitian {n:nat} (H: Square (2^n)): Prop :=
  H† = H.

(* meas_to m M ψ captures the projective measurement postulate:
  if ψ is an eigenvector of Hermitian observable M with eigenvalue m, 
  then measuring M on ψ yields m with certainty (probability = 1). *)
Definition meas_to {n} (m: C) (M: Square (2^n)) (psi: Vector (2^n)) :=
  WF_Matrix M /\ hermitian M /\ M × psi = m .* psi.

(* because every pauli operator is hermitian, 
  they can all be viewed as observable *)
Notation PauliObservable := PauliTuple.

Lemma pauli_base_hermitian:
  forall (p: PauliBase),
  @hermitian 1%nat (p1_int p).
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
  forall (operator: PauliTupleBase n), hermitian (pn_int operator).
Proof.
  rewrite /hermitian /png_int /PauliObservable //= => pt.
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
Theorem stb_meas_to_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> meas_to 1 (pn_int p) psi.
Proof.
  split => H.
  - rewrite /meas_to.
    split. apply pn_int_wf.
    split. apply pauli_hermitian.
    apply PauliOperator_stb in H.
    rewrite H. by Qsimpl.
  - move: H. 
    rewrite /meas_to => [[_ [_ H]]].
    rewrite /stb /act_n /applyP /=. Qsimpl.
    rewrite H. by Qsimpl.
Qed.

(* 
  What we are really interesting is to use pauli operator
  as observables.
 *)
Definition meas_p_to {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :=
  (pn_int P) × psi = m .* psi.
  
Theorem meas_p_to_correct {n}:
  forall (m:C) (P: PauliOperator n) (psi: Vector (2^n)),
  meas_p_to m P psi <-> meas_to m (pn_int P) psi.
Proof.
  move => m P psi.
  rewrite /meas_p_to /meas_to.
  split.
  - move => H.
    split => //. apply pn_int_wf.
    split => //. apply pauli_hermitian.
  - move => [_ [_ H]].
    exact H.
Qed. 

Lemma meas_p_to_applyP {n} (m: C) (P: PauliOperator n) (psi: Vector (2^n)) :
  meas_p_to m P psi <->
  applyP psi P = m .* psi.
Proof.
  rewrite /meas_p_to /applyP.
  by rewrite !/PauliOpToElem !png_int_one.
Qed.



Corollary stb_meas_p_to_1 {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi <-> meas_p_to 1 p psi.
Proof.
  split => HH.
  - rewrite meas_p_to_correct.
    by apply stb_meas_to_1.
  - rewrite meas_p_to_correct in HH.
    by rewrite stb_meas_to_1.
Qed.

Notation "''Meas' P 'on' psi '-->' m " := (meas_p_to m P psi)
 (at level 8) : form_scope.

(* this line is required *)
Import all_pauligroup. 

(* Example: Measure Z1Z2 on 00 yields 1. *)
Check 'Meas ([p Z, Z]) on ∣ 0, 0 ⟩ --> 1.

Section Eigenvalue. 

Lemma p1_involutive :
  forall (p: PauliBase), mulg p p = I.
Proof. by move => p; case p. Qed.

(* 
  this one should be moved to PauliProps.v
  However, the apply/eqP does not work there.
  and I don't know why.
*)
Lemma pauli_involutive {n}:
  forall (op: PauliTupleBase n),
  (mulg op op) = (id_pn n).
Proof.
  move => op.
  induction n.
  rewrite tuple0 /id_pn /=. 
  by apply /eqP.
  case: op / tupleP => h t.
  rewrite /mulg /= mult_pn_cons.
  rewrite /mulg /= in IHn.
  rewrite IHn.
  change mult_p1 with (@mulg PauliBase). 
  rewrite pn_idP.
  by rewrite p1_involutive.
Qed.

Lemma get_phase_pn_involutive n:
  forall (op: PauliTupleBase n),
  get_phase_pn op op = One.
Proof.
  move => op.
  induction n.
    by rewrite tuple0; apply /eqP.
   case: op / tupleP => h t.
   rewrite get_phase_pn_cons IHn.
   by case h.
Qed.


Lemma operator_nonzero_det:
  forall (n:nat) (op: PauliOperator n),
  Determinant (png_int op) <> 0.
Proof.
  move => n op.
  apply invertible_iff_det_neq_0.
  auto with wf_db.
  rewrite /invertible /PauliOpToElem.
  remember ((One, op): PauliElement n) as p.
  exists (png_int (invg p)).
  split.
  auto with wf_db.
  rewrite /Minv !png_int_Mmult.
  change mult_png with (@mulg (PauliElement n)).
  rewrite mulgV mulVg /=.
  rewrite id_pn_int. 
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
  remember (png_int _) as m.
  apply (involutive_eigenvalue n (png_int op) psi lambda); auto with wf_db.
  apply (operator_nonzero_det).
  subst.
  move: (pauli_involutive op).
  rewrite /mulg /= => H.
  Qsimpl.
  rewrite -pn_int_Mmult H get_phase_pn_involutive PauliProps.id_pn_int //=. 
  by Qsimpl. subst. by [].
Qed.

End Eigenvalue.

Require Import ExtraSpecs.


(* Notation Just for readability *)
Notation ErrorOperator := PauliOperator.
Notation Observable := PauliOperator.
(* A helper to let coq make type right *)

Definition t2o {n}: (n.-tuple PauliBase) -> PauliOperator n := Datatypes.id.


Lemma meas_p_to_unique {n}:
  forall (phi: Vector (2^n)) (ob: Observable n)  (r q: C),
  WF_Matrix phi ->
  'Meas ob on phi --> r ->
  'Meas ob on phi --> q ->
  phi <> Zero -> 
  r = q.
Proof.
  move => phi ob r q Hwf.
  rewrite /meas_p_to => H1 H2 Hnt.
  have: (pn_int ob × phi = pn_int ob × phi) by auto.
  rewrite {1}H1 H2.
  apply Mscale_cancel; auto.
Qed.

Lemma pn_int_concat {n m}:
  forall (op0: PauliTupleBase n) (op1: PauliTupleBase m) ,
  (pn_int [tuple of op0 ++ op1]) = 
  (pn_int op0) ⊗ (pn_int op1).
Proof.
  simpl.
  move => p q.
  induction n.
  - rewrite tuple0.
    Qsimpl. 
    + by rewrite tupleE catNil. 
  - case: p / tupleP => hp tp.
    rewrite !tupleE !catCons.
    rewrite pn_int_cons /= theadCons beheadCons IHn /=.
    rewrite /pow_add. 
    rewrite (kron_assoc (p1_int hp ) (pn_int tp) (pn_int q)); auto with wf_db.
Qed. 

Lemma applyP_kron {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Apply t2o [tuple of op0 ++ op1] on (phi0 ⊗ phi1) ) = 
  ('Apply op0 on phi0) ⊗ ('Apply op1 on phi1).
Proof.
  move => op0 op1 phi0 phi1.
  rewrite /applyP /=. Qsimpl.
  rewrite /t2o /Datatypes.id.
  rewrite pn_int_concat.
  rewrite kron_mixed_product'; try auto;
  by rewrite Nat.pow_add_r.
Qed.
(* A p = - p /\ B q = q -> (A ++ B) (q ⊗ p) = - (q ⊗ p) *)
Lemma meas_p_to_m1_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 --> (-1)) ->
  ('Meas op1 on phi1 -->  1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> (-1).
Proof.
  rewrite /meas_p_to.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite pn_int_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1 Mscale_1_l Mscale_kron_dist_l.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma meas_p_to_1m_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  1) ->
  ('Meas op1 on phi1 --> -1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> (-1).
Proof.
  rewrite /meas_p_to.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite pn_int_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma meas_p_to_11_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  1) ->
  ('Meas op1 on phi1 -->  1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> 1.
Proof.
  rewrite /meas_p_to.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite pn_int_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.

Lemma meas_p_to_mm_krons {n m}:
  forall (op0: PauliOperator n) (op1: PauliOperator m) (phi0: Vector (2^n)) (phi1: Vector (2^m)),
  ('Meas op0 on phi0 -->  -1) ->
  ('Meas op1 on phi1 -->  -1) ->
  'Meas [tuple of op0 ++ op1] on (phi0 ⊗ phi1) --> 1.
Proof.
  rewrite /meas_p_to.
  move => op0 op1 phi0 phi1 H0 H1.
  rewrite pn_int_concat.
  rewrite kron_mixed_product'; try auto.
  - by rewrite H0 H1  Mscale_kron_dist_l; lma.
  - by rewrite Nat.pow_add_r.
  - by rewrite Nat.pow_add_r.
Qed.
