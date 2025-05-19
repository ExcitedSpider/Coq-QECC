(* 
This file includes the formalization of 
  - quantum group action.
  - phase negation
  - commutativity of Pauli operators
Key definitions:
  - applyP := apply a pauli operator
*)

(* Refer to https://math-comp.github.io/htmldoc_2_2_0/mathcomp.fingroup.action.html *)
(* We do not use mathcomp's definition because it requires finite structures, but quantumLib *)
(* works on infinite structure (Hilbert Space) *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.
From QuantumLib Require Import Matrix.
Require Import WellForm.
Require Import ExtraSpecs.
Import GroupScope.

Section ActionDef.

(* aT: action operator type *)
(* D: the set of operators that is useful *)
Variables (aT : finGroupType) (D : {set aT}) (dim: nat).
(* we restraint the applied set to be the hilbert space *)
Definition ActionType := (Vector (2^dim) -> aT -> Vector (2^dim)).
Implicit Type (to : ActionType).
Implicit Type (x: Vector (2^dim)).

(* compatibility *)
Definition act_comp to x := 
  forall (a b: aT), to x (mulg b a) = to (to x a) b.

(* identity *)
Definition act_id to := forall x, WF_Matrix x -> to x (oneg aT) = x.

(* From https://mathworld.wolfram.com/GroupAction.html *)
(* A group G is said to act on a set X when 
   there is a map to : G × X -> X  such that
   for all elements x in X 
   1. to(x, e) = x where e is the id of G 
   2. to(g, to(h, x)) = to(g * h, x)
   *)
(* In addition, we introduct a well-form assumption to make *) 
(* sure x has valid physical meaning *)

Definition is_action to :=
  act_id to /\ forall x, { in D &, act_comp to x}.

Record action := Action {
  act :> Vector (2^dim) -> aT -> Vector(2^dim); 
  _ : is_action act
}.


End ActionDef.


Require Import SQIR.UnitaryOps.
Require Import PauliGroup.
Require Import PauliProps.
Import all_pauligroup.
(* An n-qubit Pauli operator is a Hermitian element of the 
n-qubit Pauli group P_n *)
(* One detail to notice is that we only consider phase +1.
Technically, phase -1 also makes an element of P_n hermitian
But they are not very useful *)
Notation PauliOperator := PauliString.

(* We use PauliElement to refer to all elements in pauli groups
  note that not all elements are pauli operator
  for phase in {-i, i}, these elements are not hermitian
*)
Notation PauliElement := PauliElement.

Definition PauliOpToElem {n} (x : PauliOperator n) : PauliElement n := (One,x).
Coercion PauliOpToElem : PauliOperator >-> PauliElement.

Definition PauliBaseToOp (x : PauliBase) : PauliElem1 := (One, x).
Coercion PauliBaseToOp : PauliBase >-> PauliElem1.

Section QuantumActions. 


(* Apply a single-qubit pauli operator *)
Definition apply1p : Vector 2 -> PauliElem1 -> Vector 2 :=
  fun psi op => (int_p1 op) × psi.

Lemma mult_phase_comp: forall a b, int_phase (a) * int_phase (b) = 
  int_phase (mul_phase a b).
Proof.
  move => a b.
  all: case a; case b; lca.
Qed.

Definition aTs := [set: PauliElem1].


Fact act_1_is_action:
  (is_action _ aTs 1 apply1p).
Proof.
  rewrite /is_action; split.
  {
    rewrite /act_id /apply1p /= => x Hwf.
    lma'.
  }
  {
    rewrite //= => x a b Ha Hb.
    case a; case b => sa pa sb pb.
    rewrite /apply1p /int_p1 /=.
    rewrite !Mscale_mult_dist_l Mscale_mult_dist_r Mscale_assoc.
    rewrite -!mult_phase_comp.
    rewrite Cmult_comm.
    rewrite -!Mmult_assoc  int_p1b_Mmult .
    rewrite Mscale_mult_dist_l.
    rewrite -!Mscale_assoc.
    rewrite /mulg //=.
    case pa; case pb;  rewrite ?Mscale_assoc //=; 
    apply Mscale_simplify; auto; lca.
  }
Qed.


Check Action.

(* Coq can infer these that depend on the final one. *)
Arguments Action {aT D dim}.

Canonical act_1 := (Action apply1p act_1_is_action).

(* Sancheck *)
Goal act_1 ∣0⟩ (% X) = ∣1⟩.
Proof.
  rewrite /= /apply1p /=.
  lma'.
Qed.


Variable (n: nat).

Definition applyP : Vector (2^n) -> PauliElement n -> Vector (2^n) :=
  fun psi op => (int_pn op) × psi.


Set Bullet Behavior "Strict Subproofs".

Definition aTsn := [set: PauliElement n].


Lemma applyP_is_action:
  is_action _ aTsn _ applyP.
Proof.
  rewrite /is_action /act_id /=.
  split.
  {
    intros x Hwf.
    rewrite /act_id /applyP id_int_pn.
    by rewrite Mmult_1_l.
  }
  {
    move => x.
    rewrite /act_comp /= /applyP.
    move => *.
    by rewrite -int_pn_Mmult Mmult_assoc.
  }
Qed.

Canonical act_n := (Action applyP applyP_is_action).

(* Had to close here awardly because we don't want n to remain variable *)
End QuantumActions.

Arguments applyP {n}.

Notation "''Apply' P 'on' psi" := (applyP psi P) (at level 200).


Definition xxx: PauliElement 3 := (One, [tuple of X :: X :: X :: []]).

(* sancheck *)
Goal act_n _ ∣0,0,0⟩ xxx = ∣1,1,1⟩.
Proof.
  rewrite /act_n /applyP /=.
  Qsimpl.
  lma'.
Qed.


Lemma applyP_plus { n: nat }:
  forall (operator: PauliElement n) (st1 st2: Vector (2^n)),
  (applyP (st1 .+ st2) operator) = 
  (applyP st1 operator) .+ (applyP st2 operator).
Proof. move => *; by rewrite /applyP Mmult_plus_distr_l. Qed.

Lemma applyP_mscale { n: nat }:
  forall (operator: PauliElement n) (st: Vector (2^n)) (a: C),
  (applyP (a .* st) operator) = 
  a.* (applyP st operator) .
Proof. move => *. by rewrite /applyP Mscale_mult_dist_r. Qed.

Lemma applyP_comb {n : nat }:
  forall (op1 op2: PauliElement n) (st: Vector (2^n)),
  applyP (applyP st op1) op2 = 
  applyP st (mulg op2 op1).
Proof.
  move: (applyP_is_action n) => [_ H] op1 op2 st.
  move: (H st) => H1.
  clear H.
  rewrite /act_comp /= in H1.
  move: (H1 op1 op2) => H.
  clear H1.
  symmetry. apply H; 
  by rewrite inE.
Qed.

Lemma applyP_id {n: nat} :
  forall (st: Vector (2^n)),
  WF_Matrix st ->
  applyP st (@oneg (PauliElement n)) = st.
Proof.
  move: (applyP_is_action n) => [H _] st.
  rewrite /act_id /= in H.
  apply H.
Qed.


Lemma apply1p_wf:
  forall (op: PauliElem1) (v: Vector 2),
  WF_Matrix v -> WF_Matrix (apply1p v op).
Proof.
  move => op v.
  rewrite /apply1p.
  apply WF_mult.
  apply int_p1_wf.
Qed.

Lemma apply_n_wf n:
  forall (op: PauliElement n) (v: Vector (2^n)),
  WF_Matrix v -> WF_Matrix (applyP v op).
Proof.
  move => op v.
  rewrite /applyP.
  apply WF_mult.
  apply int_pn_wf.
Qed.

#[export] Hint Resolve apply_n_wf apply1p_wf : wf_db.


Theorem applyP_nonzero n:
  forall (op: PauliString n) (v: Vector (2^n)),
  WF_Matrix v -> v <> Zero -> (applyP v op) <> Zero.
Proof.
  move => op v Hwf Hnz.
  apply norm_nonzero_iff_nonzero.
  apply apply_n_wf; auto.
  move: (pauli_unitary n op) => Hopu.
  eapply (unitary_preseve_norm) in Hopu.
  rewrite /applyP -Hopu.
  apply norm_nonzero_iff_nonzero; auto. 
  Unshelve. apply Hwf.
Qed.

