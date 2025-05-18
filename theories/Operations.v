Require Import PauliGroup.
Require Import QuantumLib.Quantum.
From mathcomp Require Import all_ssreflect fingroup.

Require Import WellForm.
Require Import PauliProps.
Section Operations.
Import all_pauligroup.

Definition compose_pstring {n m: nat} 
  (ps1 : PauliElement n) (ps2 : PauliElement m) : PauliElement (n + m) :=
  let s := mulg ps1.1 ps2.1 in
  let v := [tuple of ps1.2 ++ ps2.2] in
  (s, v).

Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.
  

Goal compose_pstring ([p1 X, Y]) ([p1 Z, I]) = ([p1 X, Y, Z, I]).
Proof.
  rewrite /compose_pstring /mulg /=.
  apply injective_projections.
  - by rewrite /=.
  - apply /eqP. by [].
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
    + by rewrite tupleE catNil; auto with wf_db. 
  - case: p / tupleP => hp tp.
    rewrite !tupleE !catCons.
    rewrite int_pnb_cons /= theadCons beheadCons IHn /=.
    rewrite /pow_add. 
    rewrite (kron_assoc (int_p1b hp ) (int_pnb tp) (int_pnb q)); auto with wf_db.
Qed. 

Theorem compose_pstring_correct:
  forall {n m: nat}  (ps1: PauliElement n) (ps2: PauliElement m),
  int_pn (compose_pstring ps1 ps2) =
  int_pn ps1 ⊗ int_pn ps2.
Proof.
  move => n m [p1 t1] [p2 t2].
  rewrite /compose_pstring /int_pn /=.
  rewrite Mscale_kron_dist_l Mscale_kron_dist_r.
  rewrite int_pnb_concat.
  by rewrite Mscale_assoc int_phase_comp.
Qed.

Definition pstr_negate_phase (n: nat) := (NOne, id_pn n).
Notation "-1.⊗ n" := (pstr_negate_phase n) (at level 40).

End Operations.

Section HardamardConjugation.

Notation "[[ p ]]" := (int_pn p) (at level 200): form_scope.

Definition h_conj {n:nat} (p: PauliElement n):=
   (hadamard_k n) × [[ p ]] × (hadamard_k n) .

Lemma MmultHHk {n}:
  hadamard_k n × (hadamard_k n) = I (2^n).
Proof.
  induction n.
  - rewrite /hadamard_k //=. solve_matrix.
  rewrite /=. restore_dims.
  rewrite kron_mixed_product IHn.
  rewrite MmultHH.
  rewrite id_kron.
  lma.
Qed.

(* Simplify hadamard transformation  *)
Theorem simplify_htrans {n} :
  forall (psi phi: Vector (2^n)) (p: PauliElement n),
  WF_Matrix psi ->
  [[ p ]] × psi = phi ->
  (h_conj p) × ((hadamard_k n) × psi) = (hadamard_k n) × phi.
Proof.
  move => psi phi p Hwf.
  rewrite /h_conj => H .
  rewrite -!Mmult_assoc.
  rewrite (Mmult_assoc (hadamard_k n × [[p]]) ).
  rewrite MmultHHk.
  rewrite (Mmult_assoc (hadamard_k n × [[p]]) ).
  rewrite Mmult_1_l.
  by rewrite (Mmult_assoc) H; auto.
  auto.
Qed.

Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Import all_pauligroup.

Definition z1z2 := [p Z, Z, I].

Lemma h_conj_z:
  hadamard × σz × hadamard = σx.
Proof. by solve_matrix. Qed.

(* $ H^3 Z1Z2 H^3$ = X1X2 *)
Lemma h_conj_z1z2:
  h_conj ([p1 Z, Z, I]) = [[ [p1 X, X, I] ]].
Proof.
  rewrite /h_conj /=.
  Qsimpl.
  rewrite MmultHH.
  by rewrite -!Mmult_assoc h_conj_z.
Qed.

End HardamardConjugation.
