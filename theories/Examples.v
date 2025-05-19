(* We present some examples of stabiliser code for case study. *)

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.
Require Import Stabilizer.

Require Import SQIR.UnitaryOps.
Require Import Action.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import ExtraSpecs.
Require Import Observable.
Require Export SQIR.UnitaryOps.
Require Import QECC.

Module BitFlip311.

Section VarScope.

Open Scope ucom.

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

(* This should be make more generic, but i did not find a good one *)
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

Set Bullet Behavior "Strict Subproofs".

(* The encoding program is correct *)
Theorem encode_correct :
  (uc_eval encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ )
  = α .* L0 .+ β .* L1.
Proof.
  rewrite /= /L0 /L1.
  apply encode_by_component;
  autorewrite with eval_db; simpl; Qsimpl.
  all: repeat (
    distribute_plus;
    repeat rewrite <- kron_assoc by auto with wf_db;
    restore_dims
  );
  repeat rewrite kron_mixed_product; Qsimpl;
  by autorewrite with ket_db.
Qed.

(* After verifing the encoding circuit, we can 
  work sorely on abstract codespace and pauli operator
*)
(* If two basic states are identical, inner producr is 1 *)
(* Else 0 *)
Ltac simplify_inner_product :=
  repeat match goal with
  | |- context[⟨ ?v, ?v ⟩] =>
      let H := fresh in
      assert (H: ⟨ v, v ⟩ = 1)   by lca; rewrite H; clear H
  | |- context[⟨ ?v1, ?v2 ⟩] =>
      let H := fresh in
      assert (H: ⟨ v1, v2 ⟩ = 0) by lca; rewrite H; clear H
  end.

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

Require Import PauliGroup.

Notation "[ 'set' a1 , a2 , .. , an ]" := (setU .. (a1 |: [set a2]) .. [set an]) (at level 200): form_scope.

Definition setexample := [set true, false, true ].


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
  rewrite /meas_p_to /psi;
  rewrite !Mmult_plus_distr_l !Mscale_mult_dist_r;
  rewrite /psi;
  SimplApplyPauli.
  - by replace (β * (-1) * (-1)) with (β) by lca.
  - by replace (β * (-1) * (-1)) with (β) by lca.
Qed.

Notation I2 := (Matrix.I 2).
  
(* Apply any error in BitFlipError, there is at least one Syndrome Measurement
 can detect it *)

Theorem obs_be_stabiliser_i :
  obs_be_stabiliser SyndromeMeas psi.
Proof.
  rewrite /obs_be_stabiliser => M Mmem.
    rewrite stb_meas_p_to_1.
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

Fact flip0_recover_by_x0:
  (recover_by X1 X1).
Proof. by rewrite /recover_by; apply /eqP. Qed.

Definition BitFlipCode := BuildDetectionCode 3 psi SyndromeMeas BitFlipError obs_be_stabiliser_i errors_detectable_i.

Definition PhaseFlip0: PauliOperator 3 := [p Z, I, I].

Fact phase_flip_error_effect:
  ('Apply PhaseFlip0 on psi) = (α .* L0 .+ -1 * β .* L1).

Proof. by rewrite /L0 /L1; SimplApplyPauli; lma. Qed.

(* This code is unable to detect phase flip *)
Fact undetectable_phase_flip_0: 
  undetectable BitFlipCode PhaseFlip0.
Proof.
  rewrite /undetectable /= => M.
  (* ssreflect magic *)
  rewrite !inE => /orP [/eqP -> | /eqP ->].
  - SimplApplyPauli. lma.
  - SimplApplyPauli. lma.
Qed.



Definition X23 : PauliOperator 3 := mulg X2 X3.

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

(* X1 and X23 are indistinguishable errors to this code *)
Theorem indistinguishable_X1_X23:
  indistinguishable BitFlipCode
  X1 X23.
Proof.
  move => M m.
  simpl.
  rewrite apply_X1_effect.
  assert (Hx1: ('Apply X23 on psi) = (α .* ∣0,1,1⟩ .+ β .* ∣1,0,0⟩)). {
    by SimplApplyPauli.
  }
  rewrite Hx1; clear Hx1.
  move: m.
  rewrite !inE => /orP [/eqP -> | /eqP ->] H.
  - SimplApplyPauli. lma.
  - contradict H => F.
    apply C1_neq_mC1.
    apply (meas_p_to_unique (α .* ∣ 1, 0, 0 ⟩ .+ β .* ∣ 0, 1, 1 ⟩) Z23).
    + auto with wf_db.
    + SimplApplyPauli; lma.
    + move: F. replace (RtoC (-1)) with (-C1) by lca. 
      auto.
    + apply state_nonzero.
Qed.

Definition Y1: PauliOperator dim := [p Y, I, I].

Locate negate_phase_simpl.

(* Bit flip code is not able to distinguish a bit-flip with a bit-phase-flip *)
Theorem indistinguishable_X1_Y1:
  indistinguishable BitFlipCode X1 Y1.
Proof.
  move => //= M H; move: (H) => H'; move: H.
  rewrite !inE => /orP [/eqP H | /eqP H].
  - move => _.
    apply stabiliser_detect_error.
    apply (edc_stb_mem_spec BitFlipCode); auto.
    apply Negation.negate_phase_simpl.
    rewrite H /Z12 /Y1 //=.
    by apply /eqP.
  - rewrite !apply_X1_effect => F.
    exfalso.
    apply C1_neq_mC1.
    apply (meas_p_to_unique ('Apply X1 on psi) M).
    all: try rewrite apply_X1_effect.
    + auto with wf_db.
    + rewrite H. SimplApplyPauli; lma.
    + move: F. 
      replace (RtoC (-1)) with (- C1) by lca; auto. 
    + apply state_nonzero.
Qed.

Ltac prove_undetectable E M:=
  apply (meas_p_to_unique ('Apply E on psi) M); auto;
  [ rewrite /applyP /psi; auto 10 with wf_db
  | apply stabiliser_undetectable_error;
      [ by apply (edc_stb_mem_spec BitFlipCode); rewrite !inE
      | by rewrite /M /M //=; apply /eqP ]
  | apply applyP_nonzero; try apply psi_WF; apply psi_nonzero ].

Ltac prove_detectable E M :=
  apply (meas_p_to_unique ('Apply E on psi) M); auto;
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

Definition BitFlipCorrectionCode := BuildCorrectionCode BitFlipCode bit_flip_code_unique_syndrome.

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
  rewrite /meas_p_to /psi;
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
  rewrite stb_meas_p_to_1.
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

(* Z1 is a phase flip *)
Definition Z1: PauliOperator dim := t2o [tuple of  Z :: nseq 8 I].


Lemma apply_z1_L0_effect: 
  (('Apply Z1 on L0) = ((∣0,0,0⟩ .+ -C1 .* ∣1,1,1⟩) ⊗ (2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)))).
Proof.
  rewrite kron_n_assoc; auto with wf_db.
  assert (H: Z1 = t2o [tuple of [p Z, I, I] ++ t2o (nseq 6 I)]). 
    by apply /eqP.
  rewrite H /t2o; clear H.
  rewrite (applyP_kron ([p Z, I, I])).
  rewrite applyP_plus applyP_id; restore_dims; auto with wf_db.
  apply kron_simplify; auto.
  apply Mplus_simplify.
  - by SimplApplyPauli; lma.
  - by SimplApplyPauli; lma.
Qed.

Lemma apply_z1_L1_effect: 
  (('Apply Z1 on L1) = ((∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ (2 ⨂ (∣0,0,0⟩ .+ -C1 .* ∣1,1,1⟩)))).
Proof.
  rewrite kron_n_assoc; auto with wf_db.
  assert (H: Z1 = t2o [tuple of [p Z, I, I] ++ t2o (nseq 6 I)]). 
    by apply /eqP.
  rewrite H /t2o; clear H.
  rewrite (@applyP_kron 3).
  rewrite applyP_plus applyP_id; restore_dims; auto 10 with wf_db.
  apply kron_simplify; auto.
  apply Mplus_simplify.
  - by SimplApplyPauli; lma.
  - by SimplApplyPauli; lma.
Qed.

Lemma apply_z1_effect:
('Apply Z1 on psi) = norm .* (
  α .* ((∣0,0,0⟩ .+ -C1 .* ∣1,1,1⟩) ⊗ (2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩))) .+ 
  β .* ((∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ (2 ⨂ (∣0,0,0⟩ .+ -C1 .* ∣1,1,1⟩)))).
Proof.
  rewrite /psi applyP_mscale.
  rewrite applyP_plus !applyP_mscale.
  by rewrite apply_z1_L0_effect apply_z1_L1_effect.
Qed.


Definition X123 :PauliOperator 3 := [p X, X, X].

Lemma stb_part:
  stb (X123) (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  simpl_stbn.
Qed.

Ltac unfold_stb_psi := 
  rewrite /psi;
  apply stb_scale; apply stb_addition; apply stb_scale;
  rewrite stb_meas_p_to_1 /L0 /L1; Qsimpl.

Lemma obsx12_stb:
  obsX12 ∝1 psi.
Proof.
  unfold_stb_psi.
  - rewrite kron_assoc; auto with wf_db.
    replace obsX12 with [tuple of X123 ++ ([p X, X, X, I, I, I])] by by apply /eqP.
    apply (@meas_p_to_11_krons 3 6).
    + SimplApplyPauli; lma.
    + replace ([p X, X, X, I, I, I]) with [tuple of X123 ++ (oneg (PauliOperator 3))] by by apply /eqP.
      apply (@meas_p_to_11_krons 3 3).
        by rewrite -stb_meas_p_to_1; apply stb_part.
        by rewrite meas_p_to_applyP applyP_id; auto with wf_db; Qsimpl.
  - rewrite kron_assoc; auto with wf_db.
    replace obsX12 with [tuple of X123 ++ ([p X, X, X, I, I, I])] by by apply /eqP.
    apply (@meas_p_to_mm_krons 3 6).
    + SimplApplyPauli; lma.
    + replace ([p X, X, X, I, I, I]) with [tuple of X123 ++ (oneg (PauliOperator 3))] by by apply /eqP.
      apply (@meas_p_to_m1_krons 3 3).
      + SimplApplyPauli; lma.
      + by rewrite meas_p_to_applyP applyP_id; auto with wf_db; by Qsimpl.
Qed. 

Lemma obsx12_err_state0:
  'Meas obsX12 on (∣ 0, 0, 0 ⟩ .+ - C1 .* ∣ 1, 1, 1 ⟩) ⊗ 2 ⨂ (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩)
    --> -1 .
Proof.
  replace obsX12 with [tuple of [p X, X, X] ++ ([p X, X, X, I, I, I])] by by apply /eqP.
  apply (@meas_p_to_m1_krons 3).
  - SimplApplyPauli. lma.
  - replace ([p X,  X,  X,  I,  I,  I]) with [tuple of [p X, X, X] ++ ([p I, I, I])] by by apply /eqP.
    apply (@meas_p_to_11_krons 3).
    SimplApplyPauli; lma.
    SimplApplyPauli; lma.
Qed.

Lemma obsx12_err_state1:
  'Meas obsX12 on (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩) ⊗ 2 ⨂ (∣ 0, 0, 0 ⟩ .+ -C1 .* ∣ 1, 1, 1 ⟩)
    --> -1 .
Proof.
  replace obsX12 with [tuple of [p X, X, X] ++ ([p X, X, X, I, I, I])] by by apply /eqP.
  apply (@meas_p_to_1m_krons 3).
  - SimplApplyPauli. lma.
  - replace ([p X,  X,  X,  I,  I,  I]) with [tuple of [p X, X, X] ++ ([p I, I, I])] by by apply /eqP.
    apply (@meas_p_to_m1_krons 3).
    SimplApplyPauli; lma.
    SimplApplyPauli; lma.
Qed.

Theorem obsx12_detect_phase_flip:
  'Meas obsX12 on ('Apply Z1 on psi) --> -1.
Proof.
  rewrite apply_z1_effect meas_p_to_applyP.
  rewrite !applyP_mscale !applyP_plus !applyP_mscale.
  remember (/ C2 * / √ 2) as norm.
  rewrite !Mscale_assoc (Cmult_comm _ norm) -Mscale_assoc.
  apply Mscale_simplify; auto.
  move/meas_p_to_applyP : obsx12_err_state0 => ->.
  move/meas_p_to_applyP : obsx12_err_state1 => ->.
  rewrite Mscale_plus_distr_r !Mscale_assoc.
  by rewrite !(Cmult_comm (-1)).
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

Definition X1: PauliOperator dim := t2o [tuple of X :: nseq 8 I].
Definition Y1: PauliOperator dim := t2o [tuple of Y :: nseq 8 I].
Definition BPFlipE0 := Y1.

(* Y1 is a combination of bit flip and phase flip error *)
Lemma Y1_bit_phase_flip: mulg X1 Z1 = Y1. Proof. by apply /eqP. Qed.

Lemma obsZ12_stb:
  obsZ12 ∝1 psi.
Proof.
  unfold_stb_psi.
  - rewrite kron_assoc; auto with wf_db.
    replace obsZ12 with [tuple of ([p Z, Z, I]) ++ (oneg (PauliOperator 6))] by by apply /eqP.
    apply (@meas_p_to_11_krons 3 6).
    + SimplApplyPauli; lma.
    + by rewrite meas_p_to_applyP applyP_id; auto with wf_db; Qsimpl.
  - rewrite kron_assoc; auto with wf_db.
    replace obsZ12 with [tuple of ([p Z, Z, I]) ++ (oneg (PauliOperator 6))] by by apply /eqP.
    apply (@meas_p_to_11_krons 3 6).
    + SimplApplyPauli; lma.
    + rewrite meas_p_to_applyP applyP_id; auto with wf_db; Qsimpl; auto 10 with wf_db.
Qed.

(* we show that shor's code is able to correct a bit-phase flip *)
Theorem obsZ12_detect_bit_phase_flip:
  'Meas obsZ12 on ('Apply Y1 on psi) --> -1.
Proof.
  apply stabiliser_detect_error.
  - apply obsZ12_stb.
  (* transform to group multiplication for quicker check  *)
  - by apply negate_phase_simpl; apply /eqP.
Qed.

End VarScope.

End ShorsNineQubitCode.

