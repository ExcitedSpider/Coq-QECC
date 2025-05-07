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
Require Import Assumption.

(* Simply Goals like (pn_int _ × _) *)
Ltac SimplApplyPauli := 
    rewrite ?applyP_plus ?applyP_mscale;
    rewrite ?/meas_p_to ?/applyP ?/png_int ?/pn_int /=;
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
  For pauli operators, the eigenvalue is always +-1 see `operator_eigenvalue` 
  so a error is detectable -> syndrome measurement is -1
*)
Definition detectable E := 
  let psi' := 'Apply E on psi in
    exists M,  M \in SyndromeMeas /\ 'Meas M on psi' --> -1.

Definition obs_be_stabiliser :=
  forall (M: Observable dim),
    M \in SyndromeMeas -> M ∝1 psi.

Definition errors_detectable :=
  forall (E: ErrorOperator dim),
  E \in DetectableErrors -> detectable E.


(* error E can be recovered by R *)
Definition recover_by {n} (E: ErrorOperator n) (R: PauliOperator n) :=
  mult_png R E = (@oneg (PauliElement n)).

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

Section Structure.

Record ErrorCorrectionCode := MkECC {
  dim: nat
(* Codespace *)
; psi: Vector (2^dim)
(* Observables *)
; obs: {set Observable dim}
(* Detectable Errors *)
; err: {set PauliOperator dim}
(* Obligation1: observables must be stabilisers of codespace *)
; ob1: obs_be_stabiliser obs psi 
(* Obligation2: all errors must be detectable by measurement *)
; ob2: errors_detectable obs err psi
}.

(* Undetectable is that the error state has the same measurement
  as the codespace
  There is an implicit requirement that E should be non-trivial (not I)
*)
Definition undetectable (ecc: ErrorCorrectionCode) E := 
  let psi' := 'Apply E on ecc.(psi) in
    forall M,  M \in ecc.(obs) -> 'Meas M on psi' --> 1.

(* 
Two errors are indistinguishable when all syndrome measurment
yields the same result
TODO: enforce E1 to be in the correctable error set
And derive distance of codewords based on the minimul weight of 
indistinguishable errors.
*)
Definition indistinguishable (ecc: ErrorCorrectionCode) E1 E2 :=
  forall M, M \in ecc.(obs) -> 
  let psi_e1 := 'Apply E1 on ecc.(psi) in
  let psi_e2 := 'Apply E2 on ecc.(psi) in
    ('Meas M on psi_e1 --> -1) -> ('Meas M on psi_e2 --> -1)
  .

(* The recover is trivial: simply by apply the error again.  *)
(* So we don't make them  in examples  *)
(* But we provide a theorem, see get_recover_correct *)
Definition get_recover {n}: (ErrorOperator n) -> (PauliOperator n) := Datatypes.id.

Lemma get_phase_png_involutive:
forall {n} (t: PauliOperator n), get_phase_png (One, t) (One, t) = One.
Proof.
  move => n t.
  by rewrite /get_phase_png get_phase_pn_involutive /=.
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
  t = oneg (Observable n) ->
  [tuple of I ::t] = oneg (Observable n.+1).
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
    rewrite /PauliOpToElem /=.
    rewrite /mult_png !mult_pn_cons get_phase_png_cons.
    assert (H: get_phase h h = One).
      by case h.
    rewrite H; clear H.
    change mult_phase with (@mulg phase).
    rewrite mul1g.
    assert (H: mult_p1 h h = I).
      by case h.
    rewrite H; clear H.
    move => H.
    move: (H t).
    clear H.
    rewrite !get_phase_png_involutive.
    rewrite -!png_id_simpl => H.
    apply (png_idP n).
    by rewrite H.
Qed.


End Structure.


Section Theories.

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
  png_int (mult_png Ob Er) = -C1 .* png_int (mult_png Er Ob) ->
  ('Meas Ob on ('Apply Er on psi) --> -1).
Proof.
  move => Er Ob psi Hob Hac.
  rewrite /applyP /meas_p_to -Mmult_assoc png_int_one.
  rewrite png_int_Mmult Hac Mscale_mult_dist_l.
  apply Mscale_simplify.
  rewrite /stb /act_n /= /applyP in Hob.
  rewrite -png_int_Mmult Mmult_assoc Hob. 
  by Qsimpl.
  lca.
Qed.

End Theories.