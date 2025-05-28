(* We present some examples of stabiliser code for case study. *)

Set Bullet Behavior "Strict Subproofs".

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.
Require Import Stabilizer.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import Operations.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import ExtraSpecs.
Require Import Observable.
Require Export SQIR.UnitaryOps.
Require Import QECC.
Require Import PauliProps.

Notation I2 := (Matrix.I 2).
Notation "[ 'set' a1 , a2 , .. , an ]" := (setU .. (a1 |: [set a2]) .. [set an]) (at level 200): form_scope.
Open Scope ucom.

Module BitFlip311.

Section VarScope.

Definition dim:nat := 3.

Variable (α β : C).
(* A quantum state (α .* ∣0⟩ .+ β .* ∣1⟩) is required to have norm = 1 *)
Hypothesis norm_obligation: α^* * α + β^* * β = 1.

Definition encode : base_ucom dim := 
  CNOT 0 1; CNOT 0 2.

(* The state before encoding, labeled by 'b' *)
Notation psi_b := ((α .* ∣0⟩ .+ β .* ∣1⟩)).

Notation L0 := ∣0,0,0⟩. (* Logical 0 *)
Notation L1 := ∣1,1,1⟩. (* Logical 1 *)
(* The state after encoding *)
Definition psi: Vector (2^dim) := (α .* L0.+ β .* L1).

Lemma psi_WF:
  WF_Matrix psi.
Proof. by rewrite /psi; auto with wf_db. Qed.

Lemma psi_nonzero:
  psi <> Zero.
Proof.
  move => F.
  apply inner_product_zero_iff_zero in F.
  contradict F.
  rewrite !inner_product_plus_l !inner_product_plus_r.
  rewrite !inner_product_scale_l !inner_product_scale_r.
  simplify_inner_product.
  Csimpl.
  rewrite norm_obligation.
  by nonzero.
  by rewrite/psi; auto with wf_db.
Qed.

Import all_pauligroup.

(* Verification of Code Construction (Stabilisers and Detectable Errors) *)
Section DetectionCode.

(* This lemma is not necessary in proof,  *)
(* but it makes the proof faster  *)
Lemma encode_by_component: forall (u: Square (2^dim)),
  u × (∣0⟩ ⊗ ∣0,0⟩) = L0 ->
  u × (∣1⟩ ⊗ ∣0,0⟩) = L1 ->
  u × (psi_b ⊗ ∣0,0⟩) = psi.
Proof.
  move => H0 H1 H2.
  rewrite kron_plus_distr_r Mmult_plus_distr_l.
  rewrite !Mscale_kron_dist_l !Mscale_mult_dist_r.
  by rewrite H1 H2.
Qed.

(* The encoding program is correct *)
Theorem encode_correct :
  (uc_eval encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ )
  = α .* L0 .+ β .* L1.
Proof.
  rewrite /= /L0 /L1.
  autorewrite with eval_db; simpl; Qsimpl.
  all: repeat (
    distribute_plus;
    repeat rewrite <- kron_assoc by auto with wf_db;
    restore_dims
  );
  repeat rewrite kron_mixed_product; Qsimpl;
  by autorewrite with ket_db.
Qed.

(* Set of single-qubit bit-flip error *)
Definition X1: PauliOperator 3 := [p X, I, I].
Definition X2: PauliOperator 3 := [p I, X, I].
Definition X3: PauliOperator 3 := [p I, I, X].
Definition BitFlipError: {set ErrorOperator 3 } := 
  [set X1, X2, X3].

(* Syndrome measurement *)
Definition Z12 := [p Z, Z, I].
Definition Z23 := [p I, Z, Z].
Definition SyndromeMeas: {set PauliObservable 3} :=
  [set Z12, Z23].

Close Scope group_scope.
(* Syndrome Measurement Does not change the correct code *)
Theorem SyndromeMeas_stab :
  forall (M: PauliObservable dim),
    M \in SyndromeMeas -> 'Meas M on psi --> 1.
Proof.
  move => M.
  rewrite !inE => [/orP [/eqP ->| /eqP ->]];
  rewrite /eigen_measure_p /psi;
  rewrite !Mmult_plus_distr_l !Mscale_mult_dist_r;
  rewrite /psi;
  SimplApplyPauli.
  - by replace (β * (-1) * (-1)) with (β) by lca.
  - by replace (β * (-1) * (-1)) with (β) by lca.
Qed.
  
Theorem obs_be_stabiliser_i :
  obs_be_stabiliser SyndromeMeas psi.
Proof.
  rewrite /obs_be_stabiliser => M Mmem.
    rewrite stb_eigen_measure_p_1.
    by apply SyndromeMeas_stab.
Qed.

Theorem errors_detectable_i :
  errors_detectable SyndromeMeas BitFlipError psi.
Proof.
  rewrite /errors_detectable.
  move => E.
  rewrite !inE -orb_assoc /detectable => memE.
  case/or3P: memE => HE;
  move/eqP: HE => HE;
  rewrite /=; subst;
  rewrite !applyP_plus !applyP_mscale.
  - exists Z12. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
  (* Z23 also works for X2 Error *)
  - exists Z12. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
  - exists Z23. SimplApplyPauli.
    split. by rewrite !inE eqxx. lma.
Qed.

Definition BitFlipCode := BuildDetectionCode 3 psi SyndromeMeas BitFlipError obs_be_stabiliser_i errors_detectable_i.

Print BitFlipCode.

Ltac prove_undetectable E M:=
  apply (eigen_measure_p_unique ('Apply E on psi) M); auto;
  [ rewrite /applyP /psi; auto 10 with wf_db
  | apply stabiliser_undetectable_error;
      [ by apply (edc_stb_mem_spec BitFlipCode); rewrite !inE
      | by rewrite /M /M //=; apply /eqP ]
  | apply applyP_nonzero; try apply psi_WF; apply psi_nonzero ].

Ltac prove_detectable E M :=
  apply (eigen_measure_p_unique ('Apply E on psi) M); auto;
  [ rewrite /applyP /psi; auto 10 with wf_db
  | apply (stabiliser_detect_error_c M psi E);
      [ by apply (edc_stb_mem_spec BitFlipCode); rewrite !inE
      | by apply negate_phase_simpl; apply /eqP ]
  | by apply applyP_nonzero; try apply psi_WF; apply psi_nonzero ].

(* every error in bitflip code has unique syndrome. *)
(* that is, they can be recovered *)
Theorem bit_flip_code_unique_syndrome:
  error_identified_uniquely BitFlipCode.
Proof.
  rewrite /error_identified_uniquely //= => E1 E2.
  rewrite !inE -!orb_assoc => memE1 memE2.
  case/or3P: memE1 => /eqP ->;
  case/or3P: memE2 => /eqP ->;
  move => H; try by contradict H.
  clear H.
  all: rewrite /distinguishable_by //=.
  - exists Z23 => r q _ Hr Hq.
    replace r with (C1) by prove_undetectable X1 Z23. 
    replace q with (-C1) by prove_detectable X2 Z23. 
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
  - exists Z12 => r q _ Hr Hq.
    replace r with (-C1) by prove_detectable X1 Z12. 
    replace q with (C1) by prove_undetectable X3 Z12. 
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
  - exists Z23 => r q _ Hr Hq.
    replace r with (-C1) by prove_detectable X2 Z23. 
    replace q with (C1) by prove_undetectable X1 Z23.
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
  - exists Z12 => r q _ Hr Hq.
    replace r with (-C1) by prove_detectable X2 Z12. 
    replace q with (C1) by prove_undetectable X3 Z12.
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
  - exists Z23 => r q _ Hr Hq.
    replace r with (-C1) by prove_detectable X3 Z23. 
    replace q with (C1) by prove_undetectable X1 Z23.
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
  - exists Z12 => r q _ Hr Hq.
    replace q with (-C1) by prove_detectable X2 Z12. 
    replace r with (C1) by prove_undetectable X3 Z12.
    try apply C1_neq_mC1; symmetry; apply C1_neq_mC1.
Qed.

Definition BitFlipCorrectionCode := BuildCorrectingCode BitFlipCode bit_flip_code_unique_syndrome.

End DetectionCode.

Fact flip0_recover_by_x0:
  (recover_by X1 X1).
Proof. by rewrite /recover_by; apply /eqP. Qed.
Section CodeLimitation.

Definition Z1: ErrorOperator 3 := [p Z, I, I].

Fact phase_flip_error_effect:
  ('Apply Z1 on psi) = (α .* ∣0,0,0⟩ .+ -1 * β .*∣1,1,1⟩).
Proof. by rewrite /L0 /L1; SimplApplyPauli; lma. Qed.

(* This code is unable to detect phase flip *)
Fact undetectable_phase_flip_0: 
  undetectable BitFlipCode Z1.
Proof.
  rewrite /undetectable => M.
  rewrite !inE => /orP [/eqP -> | /eqP ->].
  apply stabiliser_undetectable_error.
  + by apply stab_mem_code; auto; rewrite !inE. 
  + by apply /eqP. 
  apply stabiliser_undetectable_error.
  + by apply stab_mem_code; auto; rewrite !inE. 
  + by apply /eqP. 
Qed.

Definition X23 : PauliOperator 3 := [p I, X, X].

Lemma state_nonzero:
  α .* ∣ 1, 0, 0 ⟩ .+ β .* ∣ 0, 1, 1 ⟩ <> Zero.
Proof.
  move => F.
  apply inner_product_zero_iff_zero in F.
  contradict F.
  rewrite !inner_product_plus_l !inner_product_plus_r.
  rewrite !inner_product_scale_l !inner_product_scale_r.
  simplify_inner_product.
  Csimpl.
  rewrite norm_obligation.
  by nonzero.
  by auto with wf_db.
Qed.

Lemma apply_X1_effect:
  ('Apply X1 on psi) = (α .* ∣1,0,0⟩ .+ β .* ∣0,1,1⟩).
Proof. by SimplApplyPauli. Qed.

Lemma apply_X23_effect:
('Apply X23 on psi) = (α .* ∣0,1,1⟩ .+ β .* ∣1,0,0⟩).
Proof. by SimplApplyPauli. Qed.

(* X1 and X23 are indistinguishable errors to this code *)
Fact indistinguishable_X1_X23:
  indistinguishable BitFlipCode X1 X23.
Proof.
  unfold indistinguishable.
  move => M m.
  simpl.
  rewrite apply_X1_effect apply_X23_effect.
  split.
  {
    move: m.
    rewrite !inE => /orP [/eqP -> | /eqP ->] H.
    - SimplApplyPauli. lma.
    - contradict H => F.
      apply C1_neq_mC1.
      apply (eigen_measure_p_unique (α .* ∣ 1, 0, 0 ⟩ .+ β .* ∣ 0, 1, 1 ⟩) Z23).
      + auto with wf_db.
      + SimplApplyPauli; lma.
      + move: F. replace (RtoC (-1)) with (-C1) by lca. 
        auto.
      + rewrite -apply_X1_effect.
        apply (applyP_nonzero _ _ _ psi_WF psi_nonzero).
  }
  {
    move: m.
    rewrite !inE => /orP [/eqP -> | /eqP ->] H.
    - SimplApplyPauli. lma.
    - contradict H => F.
      apply C1_neq_mC1.
      apply (eigen_measure_p_unique (α .* ∣ 0, 1, 1 ⟩ .+ β .* ∣ 1, 0, 0 ⟩) Z23).
      + auto with wf_db.
      + SimplApplyPauli; lma.
      + move: F. replace (RtoC (-1)) with (-C1) by lca. 
        auto.
      + rewrite -apply_X23_effect.
        apply (applyP_nonzero _ _ _ psi_WF psi_nonzero).
  }
Qed.

(* Bit flip code is not able to distinguish a bit-flip with a bit-phase-flip *)
(* Definition Y1: PauliOperator dim := [p Y, I, I].

Locate negate_phase_simpl.

Theorem indistinguishable_X1_Y1:
  indistinguishable BitFlipCode X1 Y1.
Proof.
  move => //= M H; move: (H) => H'; move: H.
  rewrite !inE => /orP [/eqP H | /eqP H].
  - move => _.
    apply stabiliser_detect_error.
    apply (edc_stb_mem_spec BitFlipCode); auto.
    apply negate_phase_simpl.
    rewrite H /Z12 /Y1 //=.
    by apply /eqP.
  - rewrite !apply_X1_effect => F.
    exfalso.
    apply C1_neq_mC1.
    apply (eigen_measure_p_unique ('Apply X1 on psi) M).
    all: try rewrite apply_X1_effect.
    + auto with wf_db.
    + rewrite H. SimplApplyPauli; lma.
    + move: F. 
      replace (RtoC (-1)) with (- C1) by lca; auto. 
    + apply state_nonzero.
Qed. *)

End CodeLimitation.

End VarScope.

End BitFlip311.

Module PhaseFlip311.

Section VarScope.

Open Scope ucom.

Definition dim:nat := 3.

Variable (α β : C).

Hypothesis norm_obligation: α^* * α + β^* * β = 1.

Definition basis_change_x: base_ucom dim :=
  H 0; H 1; H 2.

Definition encode : base_ucom dim := 
  BitFlip311.encode;
  basis_change_x.

(* The state before encoding, labeled by 'b' *)
Notation psi_b := ((α .* ∣0⟩ .+ β .* ∣1⟩)).

Notation L0 := (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩). (* Logical 0 *)
Notation L1 := (∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩). (* Logical 1 *)

Definition psi: Vector (2^dim) := (α .* L0.+ β .* L1).

Notation "H^⊗3" := (hadamard ⊗ hadamard ⊗ hadamard).

(* Let's prove program `encode` change psi_b to psi *)

(* get the unitary semantics of basis change circuit *)
Lemma basis_change_unitary:
  (uc_eval basis_change_x) = H^⊗3.
Proof.
  rewrite /basis_change_x.
  simpl.
  autorewrite with eval_db; Qsimpl; simpl.
  replace (I 4) with (I 2 ⊗ I 2) by apply id_kron.
  restore_dims.
  rewrite -kron_assoc; auto with wf_db.
  by repeat rewrite kron_mixed_product; Qsimpl.
Qed.

Lemma basis_change_state:
  forall (subprog: base_ucom dim) (encoded_b: Vector (2^dim)),
  (uc_eval subprog) × (psi_b ⊗ ∣0,0⟩) = encoded_b ->
  (uc_eval (subprog; basis_change_x)) × (psi_b ⊗ ∣0,0⟩) = H^⊗3 × encoded_b.
Proof.
  move => subprog encoded_b H.
  replace 
    (uc_eval (subprog; basis_change_x))
    with ((uc_eval basis_change_x) × (uc_eval subprog))
    by easy.
  by rewrite Mmult_assoc H basis_change_unitary.
Qed.

Notation bit_flip_code := (α .* ∣0,0,0⟩ .+ β .* ∣1,1,1⟩).

(* use privious two lemmas to help us verify this *)
Theorem encode_correct:
  (uc_eval encode) × (psi_b ⊗ ∣0,0⟩) = psi.
Proof.
  rewrite /encode.
  assert (Hr: psi = H^⊗3 × bit_flip_code).
  {
    rewrite /psi Mmult_plus_distr_l !Mscale_mult_dist_r.
    rewrite !kron_mixed_product !H0_spec !H1_spec.
    replace (/ √ 2 .* ∣ 0 ⟩ .+   / √ 2 .* ∣ 1 ⟩) with ∣+⟩ by solve_matrix.
    replace (/ √ 2 .* ∣ 0 ⟩ .+ - / √ 2 .* ∣ 1 ⟩) with ∣-⟩ by solve_matrix.
    easy.
  }
  rewrite Hr. clear Hr.
  apply basis_change_state.
  apply BitFlip311.encode_correct.
Qed.

Import all_pauligroup.

Notation "[ 'set' a1 , a2 , .. , an ]" := (setU .. (a1 |: [set a2]) .. [set an]) (at level 200): form_scope.
(* TODO let's talk about how stabiliser will change *)
Definition X12 := [p X, X, I].
Definition X23 := [p I, X, X].
Definition SyndromeMeas: {set PauliObservable 3} :=
  [set X12, X23].

(* move them to somewhere suits *)
Lemma MmultXPl: σx × ∣+⟩ =       ∣+⟩. Proof. by solve_matrix. Qed.
Lemma MmultXMi: σx × ∣-⟩ = -1 .* ∣-⟩. Proof. by solve_matrix. Qed.

Close Scope group_scope.

Theorem meas_codespace_1 :
  forall (M: PauliObservable dim),
    M \in SyndromeMeas -> 'Meas M on psi --> 1.
Proof.
  move => M.
  rewrite !inE => /orP [/eqP -> | /eqP ->];
  rewrite /eigen_measure_p /psi;
  rewrite !Mmult_plus_distr_l !Mscale_mult_dist_r;
  rewrite /psi;
  SimplApplyPauli;
  rewrite !MmultXMi !MmultXPl;
  SimplApplyPauli;
  by replace (β * (-1) * (-1)) with (β) by lca.
Qed.

(* In fact there is an easier proof *)
Corollary obs_be_stabiliser_i :
  obs_be_stabiliser SyndromeMeas psi.
Proof.
  move => M.
  rewrite stb_eigen_measure_p_1.
  apply meas_codespace_1.
Qed.

Definition Z1: PauliOperator 3 := [p Z, I, I].
Definition Z2: PauliOperator 3 := [p I, Z, I].
Definition Z3: PauliOperator 3 := [p I, I, Z].
Definition PhaseFlipError: {set ErrorOperator 3 } := 
  [set Z1, Z2, Z3].

Theorem errors_detectable_i:
  errors_detectable SyndromeMeas PhaseFlipError psi.
Proof.
  rewrite /errors_detectable => E.
  rewrite !inE -orb_assoc /detectable => memE.
  case/or3P: memE => /eqP ->.
  
  exists X12. split. by rewrite !inE. 
  apply stabiliser_detect_error.
  apply obs_be_stabiliser_i. by rewrite !inE.
  simpl; Qsimpl; lma.
  
  exists X12. split. by rewrite !inE. 
  apply stabiliser_detect_error.
  apply obs_be_stabiliser_i. by rewrite !inE.
  simpl; Qsimpl; lma.

  exists X23. split. by rewrite !inE. 
  apply stabiliser_detect_error.
  apply obs_be_stabiliser_i. by rewrite !inE.
  simpl; Qsimpl; lma.
Qed.

Definition PhaseFlipCode := BuildDetectionCode 3 psi SyndromeMeas PhaseFlipError obs_be_stabiliser_i errors_detectable_i.

Definition BitFlip0: PauliOperator 3:= [p X, I, I].

Check undetectable.

(* this 3-1-1 phase flip code cannot detect a bit flip error *)
Theorem undetectable_bitflip:
 undetectable PhaseFlipCode BitFlip0.
Proof.
  apply undetectable_sufficient.
  move => //= s.
  by rewrite /BitFlip0 !inE /= => /orP [/eqP -> | /eqP ->]; apply /eqP.
Qed.

End VarScope.

End PhaseFlip311.

Module ShorsNineQubitCode. 
Set Bullet Behavior "Strict Subproofs".

Section VarScope.

Import all_ssreflect.

(* This is for solving some notation conflicts *)
Notation I := P1BaseGroup.I.
Notation X := P1BaseGroup.X.
Notation Z := P1BaseGroup.Z.
Notation Y := P1BaseGroup.Y.

Variable (α β: C).

Definition dim:nat := 9.

(* For a proper renderred expression: https://errorcorrectionzoo.org/c/shor_nine *)
Notation L0 := (3 ⨂ (∣0,0,0⟩ .+       ∣1,1,1⟩)).
Notation L1 := (3 ⨂ (∣0,0,0⟩ .+ -C1.* ∣1,1,1⟩)).
Notation norm := (/C2 * /√ 2).

Definition psi: Vector (2^dim) := norm .* (α .* L0 .+ β .* L1).

(* This could be made generic *)
Lemma applyP_linear:
  forall (E: PauliOperator dim) (L0' L1': Vector (2^dim)),
  ('Apply E on L0) = L0' ->
  ('Apply E on L1) = L1' ->
  ('Apply E on psi) = norm .* (α .* L0' .+ β .* L1').
Proof.
  move => E L0' L1'.
  rewrite /psi.
  rewrite !applyP_mscale applyP_plus !applyP_mscale.
  by move => -> ->.
Qed.

Definition obsX12: PauliOperator 9 := [p X, X, X, X, X, X, I, I, I].
Definition obsZ12: PauliOperator 9 := [p Z, Z, I, I, I, I, I, I, I].

Definition X1: PauliOperator dim := t2o [tuple of X :: nseq 8 I].
Definition Z1: PauliOperator dim := t2o [tuple of Z :: nseq 8 I].
Definition Y1: PauliOperator dim := t2o [tuple of Y :: nseq 8 I].
(*  
This set contains a representative Pauli basis for single-qubit errors on qubit 1.
  The ability to distinguish these errors implies that the code can correct
  an arbitrary single-qubit error, due to the linearity of quantum error correction.
*)
Definition ShorErrorBasis := [set X1, Z1, Y1 ].

Definition X123 :PauliOperator 3 := [p X, X, X].

Lemma stb_part:
  stb (X123) (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  simpl_stbn.
Qed.

Ltac unfold_stb_psi := 
  rewrite /psi;
  apply stb_scale; apply stb_addition; apply stb_scale;
  rewrite stb_eigen_measure_p_1 /L0 /L1; Qsimpl.

Lemma obsx12_stb:
  obsX12 ∝1 psi.
Proof.
  unfold_stb_psi.
  - rewrite kron_assoc; auto with wf_db.
    replace obsX12 with [tuple of X123 ++ ([p X, X, X, I, I, I])] by by apply /eqP.
    apply (@eigen_measure_p_11_krons 3 6).
    + SimplApplyPauli; lma.
    + replace ([p X, X, X, I, I, I]) with [tuple of X123 ++ (oneg (PauliOperator 3))] by by apply /eqP.
      apply (@eigen_measure_p_11_krons 3 3).
        by rewrite -stb_eigen_measure_p_1; apply stb_part.
        by rewrite eigen_measure_p_applyP applyP_id; auto with wf_db; Qsimpl.
  - rewrite kron_assoc; auto with wf_db.
    replace obsX12 with [tuple of X123 ++ ([p X, X, X, I, I, I])] by by apply /eqP.
    apply (@eigen_measure_p_mm_krons 3 6).
    + SimplApplyPauli; lma.
    + replace ([p X, X, X, I, I, I]) with [tuple of X123 ++ (oneg (PauliOperator 3))] by by apply /eqP.
      apply (@eigen_measure_p_m1_krons 3 3).
      by SimplApplyPauli; lma.
      by rewrite eigen_measure_p_applyP applyP_id; auto with wf_db; by Qsimpl.
Qed. 


(* Now we do it again but using error correct condition *)
(* It's so much easier *)
(* maybe we can define the negation more properly *)
Theorem obsx12_detect_phase_flip':
  'Meas obsX12 on ('Apply Z1 on psi) --> -1.
Proof.
  apply stabiliser_detect_error.
  - apply obsx12_stb.
  - rewrite /=.  
    rewrite Mscale_assoc.
    by replace (- C1 * Ci) with (-Ci) by lca.
Qed.


Lemma obsZ12_stb:
  obsZ12 ∝1 psi.
Proof.
  unfold_stb_psi.
  - rewrite kron_assoc; auto with wf_db.
    replace obsZ12 with [tuple of ([p Z, Z, I]) ++ (oneg (PauliOperator 6))] by by apply /eqP.
    apply (@eigen_measure_p_11_krons 3 6).
    + SimplApplyPauli; lma.
    + by rewrite eigen_measure_p_applyP applyP_id; auto with wf_db; Qsimpl.
  - rewrite kron_assoc; auto with wf_db.
    replace obsZ12 with [tuple of ([p Z, Z, I]) ++ (oneg (PauliOperator 6))] by by apply /eqP.
    apply (@eigen_measure_p_11_krons 3 6).
    + SimplApplyPauli; lma.
    + rewrite eigen_measure_p_applyP applyP_id; auto with wf_db; Qsimpl; auto 10 with wf_db.
Qed.

Definition measuring_different (M: PauliObservable 9) psi_1 psi_2 :=
  ('Meas M on psi_1--> C1) /\ ('Meas M on psi_2 --> -C1) \/
  ('Meas M on psi_1--> -C1) /\ ('Meas M on psi_2 --> C1).

Create HintDb shordb.
Hint Resolve obsx12_stb obsZ12_stb : shordb.

Lemma measuring_different_comm:
  forall (M: PauliObservable 9) psi_1 psi_2, 
  measuring_different M psi_2 psi_1 -> measuring_different M psi_1 psi_2.
Proof. 
  rewrite /measuring_different => M p1 p2 H.
  case H => Hcase.
  right. apply and_comm.
  by apply Hcase.
  left. apply and_comm.
  by apply Hcase.
Qed.
  
Lemma distinguish_xz:
  measuring_different obsZ12 ('Apply X1 on psi) ('Apply Z1 on psi).
Proof.
  rewrite /measuring_different. right. split.
  apply stabiliser_detect_error_by_negate; auto with shordb.
  by apply /eqP.
  apply stabiliser_undetectable_error; auto with shordb.
  by apply /eqP.
Qed.

Lemma distinguish_xy:
  measuring_different obsX12 ('Apply X1 on psi) ('Apply Y1 on psi).
Proof.
  rewrite /measuring_different. left. split.
  apply stabiliser_undetectable_error; auto with shordb.
  by apply /eqP.
  apply stabiliser_detect_error_by_negate; auto with shordb.
  by apply /eqP.
Qed.

Lemma distinguish_zy:
  measuring_different obsZ12 ('Apply Z1 on psi) ('Apply Y1 on psi).
Proof.
  rewrite /measuring_different. left. split.
  apply stabiliser_undetectable_error; auto with shordb.
  by apply /eqP.
  apply stabiliser_detect_error_by_negate; auto with shordb.
  by apply /eqP.
Qed.

Theorem pauli_basis_distinguishable:
  forall (E1 E2: ErrorOperator 9),
  E1 \in ShorErrorBasis -> E2 \in ShorErrorBasis -> E1 <> E2 ->
  let psi_e1 := 'Apply E1 on psi in
  let psi_e2 := 'Apply E2 on psi in
  exists (M: PauliObservable 9), 
    M ∝1 psi /\ measuring_different M psi_e1 psi_e2 .
Proof.
  (* unfold the case analysis *)
  move => E1 E2.
  rewrite !inE -!orb_assoc => memE1 memE2.
  case/or3P: memE1 => /eqP ->;
  case/or3P: memE2 => /eqP ->;
  move => H; try by contradict H.
  (* start analysis *)
  all: rewrite //=.
  - exists obsZ12. split; auto with shordb.
    apply distinguish_xz.
  - exists obsX12; split; auto with shordb.
    apply distinguish_xy.
  - exists obsZ12; split; auto with shordb.
    apply measuring_different_comm.
    apply distinguish_xz.
  - exists obsZ12; split; auto with shordb.
    apply distinguish_zy.
  - exists obsX12; split; auto with shordb.
    apply measuring_different_comm.
    apply distinguish_xy.
  - exists obsZ12; split; auto with shordb.
    apply measuring_different_comm.
    apply distinguish_zy.
Qed.

End VarScope.

End ShorsNineQubitCode.

