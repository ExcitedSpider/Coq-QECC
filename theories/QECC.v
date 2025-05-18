(* We present some examples of stabiliser code for case study. *)
(* TODO: add examples for 
  - pauli operator 
  - stabilizer 
*)

From mathcomp Require Import all_ssreflect ssrbool 
ssrfun eqtype ssrnat div seq tuple finset fingroup.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Quantum.
Require Import Stabilizer.

Require Import Action.
Require Import PauliGroup.
Import all_pauligroup.
Require Import WellForm.
Require Import Observable.

(* Simply Goals like (int_pnb _ × _) *)
Ltac SimplApplyPauli := 
    rewrite ?applyP_plus ?applyP_mscale;
    rewrite ?/meas_p_to ?/applyP ?/int_pn ?/int_pnb /=;
    Qsimpl;
    repeat (
      distribute_plus;
      repeat rewrite <- kron_assoc by auto with wf_db;
      restore_dims
    );
    rewrite ?Mmult_plus_distr_l ?kron_mixed_product; Qsimpl;
    autorewrite with ket_db.

(* Notation for applying an operator on a state *)
Section QECCTheories.

Variable (dim: nat).

Variable (SyndromeMeas: {set (PauliOperator dim)}).
Variable (DetectableErrors: {set (PauliOperator dim)}).
Variable (psi: Vector (2^dim)).

(* 
  SyndromeMeas_stab shows that for all codewords,
  The measurement result is 1.
  Therefore, if we find any other measurement result, 
  we say the error is _detectable_.

  And since -1 is not 
  For pauli operators, the eigenvalue is always +-1 see `operator_eigenvalue` 
  so a error is detectable -> syndrome measurement is -1
*)
Definition detectable E := 
  let psi' := 'Apply E on psi in
    exists M,  M \in SyndromeMeas /\ 'Meas M on psi' --> -1.

Definition obs_be_stabiliser :=
  forall (M: PauliObservable dim),
    M \in SyndromeMeas -> M ∝1 psi.

Definition errors_detectable :=
  forall (E: ErrorOperator dim),
  E \in DetectableErrors -> detectable E.

(* If detectable, then there is a measurement that produces non-1 result *)
(* This is strong enough, but it might appear to be interesting  *)
(* to do the necessary proof by using operator_eigenvalue *)
Theorem detectable_correct :
  forall E, 
  detectable E -> 
  let psi' := 'Apply E on psi in
    exists M m,  M \in SyndromeMeas /\ 'Meas M on psi' --> m /\ m <> 1.
Proof.
  move => //= E.
  rewrite /detectable => [[M [H0 H1]]].
  exists M, (-1).
  repeat try (split; auto).
  move => F.
  inversion F.
  contradict H2.
  discrR.
Qed.

(* error E can be recovered by R *)
Definition recover_by {n} (E: ErrorOperator n) (R: PauliOperator n) :=
  mul_pn R E = (@oneg (PauliElement n)).

(* Apply the error then the recover, the original state is restored *)
Theorem recover_by_correct {n} :
  forall (E: ErrorOperator n) (R: PauliOperator n) (phi: Vector (2^n)),
  WF_Matrix phi ->
  recover_by E R -> 
  let phi' := 'Apply E on phi in
  ('Apply R on phi') = phi.
Proof.
  rewrite /= => E R phi Hwf.
  rewrite /recover_by.
  rewrite applyP_comb /= /mulg /=.
  move => ->.
  rewrite /oneg /=.
  apply (applyP_id).
  apply Hwf.
Qed.

(* Have to end here to make record *)
End QECCTheories.

Arguments obs_be_stabiliser {dim}.
Arguments errors_detectable {dim}.

Section DetectionCode.

(* EDC represents a code structure in which the code space is `code`
 EDC  can detect errors \in err using stabiliser observables \in obs *)
Record ErrorDetectionCode := BuildDetectionCode {
  dim: nat
(* Codespace *)
; code: Vector (2^dim)
(* Observables *)
; obs: {set PauliObservable dim}
(* Detectable Errors *)
; err: {set PauliOperator dim}
(* Obligation1: observables must be stabilisers of codespace *)
; ob1: obs_be_stabiliser obs code 
(* Obligation2: all errors must be detectable by measurement *)
; ob2: errors_detectable obs err code
}.

(* Undetectable is that the error state has the same measurement
  as the codespace
  There is an implicit requirement that E should be non-trivial (not I)
*)
Definition undetectable (edc: ErrorDetectionCode) E := 
  let psi' := 'Apply E on edc.(code) in
    forall M,  M \in edc.(obs) -> 'Meas M on psi' --> 1.

End DetectionCode.

Section ErrorCorrectionCode.

(* 
Two errors are indistinguishable when all syndrome measurment
yields the same result
TODO: enforce E1 to be in the correctable error set
And derive distance of codewords based on the minimul weight of 
indistinguishable errors.
*)
Definition indistinguishable (edc: ErrorDetectionCode) E1 E2 :=
  forall M, M \in edc.(obs) -> 
  let psi_e1 := 'Apply E1 on edc.(code) in
  let psi_e2 := 'Apply E2 on edc.(code) in
    ('Meas M on psi_e1 --> -1) -> ('Meas M on psi_e2 --> -1)
  .

(* The recover is trivial: simply by apply the error again.  *)
(* So we don't make them  in examples  *)
(* But we provide a theorem, see get_recover_correct *)
Definition get_recover {n}: (ErrorOperator n) -> (PauliOperator n) := Datatypes.id.

(* we say two errors E1 E2 are distinguishable by M *)
(* if they produce different measurement result *)
Definition distinguishable_by (edc: ErrorDetectionCode) E1 E2 M :=
forall r q,
  let psi_e1 := 'Apply E1 on edc.(code) in
  let psi_e2 := 'Apply E2 on edc.(code) in
    M \in edc.(obs) -> 
    ('Meas M on psi_e1 --> r) -> 
    ('Meas M on psi_e2 --> q) -> 
    r <> q.

(* 
An error correction code ECC is a detection code that satisfies:
- error_identified_uniquely: every error E in the error set can be detect
  by a unique syndrome  
*)
Definition error_identified_uniquely (edc: ErrorDetectionCode): Prop := 
  forall (E1 E2: PauliOperator (dim edc)), 
    E1 \in edc.(err) -> E2 \in edc.(err) -> 
    E1 <> E2 -> 
    ( exists M, distinguishable_by edc E1 E2 M ).

Record ErrorCorrectionCode := BuildCorrectionCode {
  edc :> ErrorDetectionCode;
  correction_obligation: error_identified_uniquely edc
}.

End ErrorCorrectionCode.

Section Theories.

Lemma rel_phase_n_involutive:
forall {n} (t: PauliOperator n), rel_phase_n (One, t) (One, t) = One.
Proof.
  move => n t.
  by rewrite /rel_phase_n rel_phase_pn_involutive /=.
Qed.

Lemma png_id_simpl:
forall {n} (t: PauliOperator n),
  (t = (oneg (PauliOperator n))) <-> ((One, t) = (oneg (PauliElement n)) ).
Proof.
  split.
  - move => H.
    by rewrite H /oneg /=.
  - rewrite /oneg /= /id_png => H.
    by inversion H; subst.
Qed.

Lemma png_idP:
  forall n (t: PauliOperator n),
  t = oneg (PauliObservable n) ->
  [tuple of I ::t] = oneg (PauliObservable n.+1).
Proof.
  move => n t ->.
  rewrite /oneg /= /id_pn /=.
  (* weird proof because of mathcomp weirdness *)
  apply: eq_from_tnth=> i;
  by rewrite !(tnth_nth I) /=.
Qed.

Theorem get_recover_correct {n}:
  forall (E: ErrorOperator n), 
  recover_by E (get_recover E).
Proof.
  rewrite /recover_by /get_recover /Datatypes.id /=.
  induction n.
  - move => E.
    rewrite tuple0 /recover_by.
    by apply /eqP.
  - move => E.
    case: E/tupleP => h t.
    move: IHn.
    rewrite /recover_by /=.
    rewrite /PauliOpToElem //=.
    rewrite /mul_pn. rewrite /mulg //= !mul_pnb_cons rel_phase_n_cons.
    assert (H: rel_phase h h = One).
      by case h.
    rewrite H; clear H.
    change mul_phase with (@mulg phase).
    rewrite mul1g.
    assert (H: mul_p1b h h = I).
      by case h.
    rewrite H; clear H.
    move => H.
    move: (H t).
    clear H.
    rewrite !rel_phase_n_involutive.
    rewrite -!png_id_simpl => H.
    apply (png_idP n).
    by rewrite H.
Qed.





(*
  This theorem formalizes the **error detection condition** in stabilizer theory.

  It states that if:
    1. The observable `Ob` stabilizes the state `psi` (i.e., measuring `Ob` on `psi` always yields 1), and
    2. The error operator `Er` anticommutes with `Ob`,

  then:
    - The corrupted state `Er ψ` becomes a -1 eigenstate of `Ob`, 
      meaning `Ob` can detect the presence of the error by flipping the measurement outcome.

  This theorem is extremely valuable in verification: 
  to check whether an error `Er` is detectable by a stabilizer `Ob`, 
  we **only need to test whether `Er` anticommutes with `Ob`** — no need to simulate or compute over the entire quantum state space. 
  This greatly reduces both conceptual and computational effort in formal verification of quantum error-correcting codes.
*)
Theorem stabiliser_detect_error {n}:
  forall (Ob: PauliOperator n) (psi: Vector (2^n)) (Er: PauliOperator n) ,
  Ob ∝1 psi -> 
  int_pn (mul_pn Ob Er) = -C1 .* int_pn (mul_pn Er Ob) ->
  ('Meas Ob on ('Apply Er on psi) --> -1).
Proof.
  move => Ob psi Er Hob Hac.
  rewrite /applyP /meas_p_to -Mmult_assoc int_pn_one.
  rewrite int_pn_Mmult Hac Mscale_mult_dist_l.
  apply Mscale_simplify.
  rewrite /stb /act_n /= /applyP in Hob.
  rewrite -int_pn_Mmult Mmult_assoc Hob. 
  by Qsimpl.
  lca.
Qed.

Close Scope group_scope.
(* this one explicitly use complex numbers to make it more usable *)
Corollary stabiliser_detect_error_c {n}:
  forall (Ob: PauliOperator n) (psi: Vector (2^n)) (Er: PauliOperator n) ,
  Ob ∝1 psi -> 
  int_pn (mul_pn Ob Er) = -C1 .* int_pn (mul_pn Er Ob) ->
  ('Meas Ob on ('Apply Er on psi) --> -C1).
Proof.
  assert (RtoCrw: -C1 = (RtoC (-1))) by lca. 
  rewrite {2}RtoCrw.
  apply stabiliser_detect_error. 
Qed.

(* On the opposite of error detection condition *)
(* If an stabiliser S conmmute with the error E *)
(* then this S is not able to detect the E      *)
Theorem stabiliser_undetectable_error {n}:
  forall (Ob: PauliOperator n) (psi: Vector (2^n)) (Er: PauliOperator n) ,
  Ob ∝1 psi -> 
  mul_pn Ob Er = mul_pn Er Ob ->
  ('Meas Ob on ('Apply Er on psi) --> 1).
Proof.
  move => Ob psi Er Hob Hac.
  rewrite /applyP /meas_p_to -Mmult_assoc !int_pn_one.
  rewrite int_pn_Mmult Hac; Qsimpl.
  rewrite -int_pn_Mmult.
  rewrite /stb /act_n /= /applyP in Hob.
  rewrite -{2}Hob.
  by rewrite Mmult_assoc.
Qed.


(* The specification of a member of stabilizer *)
(* if M is an observer of edc: edc, then M stabilize edc.psi *)
Corollary edc_stb_mem_spec:
  forall (edc: ErrorDetectionCode) (M: PauliObservable edc.(dim)),
  M \in edc.(obs) -> M ∝1 edc.(code).
Proof.
  move => edc M H.
  move: edc.(ob1).
  rewrite /obs_be_stabiliser => Hob.
  apply (Hob).
  apply H.
Qed.

(* If all stabiliser in a edc cannot detect an error,
then the error is not detectable *)
Corollary undetectable_sufficient 
  (edc: ErrorDetectionCode) (Er: PauliOperator edc.(dim)):
  (forall (s: PauliObservable edc.(dim)), 
    s \in edc.(obs) -> mul_pn s Er = mul_pn Er s
  ) ->
  undetectable edc Er.
Proof.
  rewrite /undetectable.
  move => H M Hm.
  apply stabiliser_undetectable_error.
  move: edc.(ob1). 
  rewrite /obs_be_stabiliser => Hstb'; auto.
  by apply H; auto.
Qed.

End Theories.