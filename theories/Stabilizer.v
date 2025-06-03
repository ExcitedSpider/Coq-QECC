(* The quantum stabilizer theories and examples          *)
(* also provided some ltacs to prove stabilize relations *) 


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq tuple.
From mathcomp Require Import fintype bigop finset fingroup morphism perm.

Require Import SQIR.UnitaryOps.
From QuantumLib Require Import Complex.
Require Import Action.
Require Import PauliGroup.
Import P1BaseGroup.
Import P1Group.
Import PNBaseGroup.
Import PNGroup.
Require Import WellForm.
Require Import ExtraSpecs.
Require Import Commutativity.

Require Import Operations.


Notation "[ 'p' x1 , .. , xn ]" := [tuple of x1 :: .. [:: xn] ..] (at level 200): form_scope.

(* When you have trivial phase 1, use this *)
Notation "[ 'p1' x1 , .. , xn ]" := (One, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-1' x1 , .. , xn ]" := (NOne, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'pi' x1 , .. , xn ]" := (Img, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Notation "[ 'p-i' x1 , .. , xn ]" := (NImg, [tuple of x1 :: .. [:: xn] ..]) (at level 200): form_scope.

Definition stab {n:nat} (pstring: PauliElement n) (psi: Vector (2^n)):= 
  act_n n psi pstring = psi.
(* A fancy symbol for "stabilize" *)
Notation "pstring ∝1 ψ" := (stab pstring ψ) (at level 50).

Definition stab_1 (p: PauliBase) (psi: Vector 2) :=
  act_1 psi (One, p) = psi.

(* TODO: Move to stabiliser.v *)
Section HermitianOperator.

Lemma PauliOperator_stab {n}:
  forall (p: PauliOperator n) (psi: Vector (2^n)),
  p ∝1 psi -> (int_pnb p) × psi = psi. 
Proof.
  rewrite /stab /= /Action.applyP /int_pn /= => p psi.
  move => H.
  rewrite Mscale_1_l in H.
  by exact H.
Qed.

End HermitianOperator.

Ltac simpl_stabn := 
  rewrite /stab /act_n /applyP /=;
  Qsimpl;
  try (lma'; try (apply apply_n_wf);auto with wf_db).

(* Z stabilises ∣0⟩ *)
Example stab_z0:
  [p1 Z] ∝1 ∣0⟩.
Proof. by simpl_stabn. Qed.

Example stab_z1:
  [p-1 Z] ∝1 ∣1⟩.
Proof. by simpl_stabn. Qed.

(* this proof can scale to two and three qubits *)
Example stab_z00:
  (One, [p Z , Z]) ∝1 ∣0,0⟩.
Proof. by simpl_stabn. Qed.

(* For length >= 4, it becomes unscalable *)
Example stab_z0000:
  [p1 Z,Z,Z,Z] ∝1 ∣0,0,0,0⟩.
Proof. 
Fail Timeout 1 by simpl_stabn. 
Abort.

Example stab_y0:
  [p1 Y] ∝1  ∣R⟩.
Proof. by simpl_stabn. Qed.

Example stab_y1:
  [p-1 Y] ∝1 ∣L⟩.
Proof. by simpl_stabn. Qed.

Example stab_x0:
  [p1 X] ∝1 ∣+⟩.
Proof. by simpl_stabn. Qed.

Example stab_x1:
  [p-1 X] ∝1 ∣-⟩.
Proof. by simpl_stabn. Qed.

(* this does not auto applied because of a hypothesiss *)
Lemma stab_id:
  forall psi,
  WF_Matrix psi -> [p1 I] ∝1 psi.
Proof.
  move => psi H.
  rewrite /stab /act_n /= /applyP.
  rewrite /int_pn /int_pnb /=.
  Qsimpl; auto.
Qed.

#[export] Hint Resolve stab_z0 stab_z1 stab_y0 stab_y1 stab_x0 stab_x1 stab_id : stab_db.


Lemma one_stab_everything:
  forall {n: nat} (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stab (id_png n) ψ.
Proof.
  intros.
  unfold stab. 
  (* This is how you get obligations *)
  case act_n => to obligations.
  simpl.
  case obligations => act_to_id _.
  by apply act_to_id.
Qed.


Open Scope group_scope.
(* If S∣ψ⟩=∣ψ⟩, then (S^(-1))∣ψ⟩=∣ψ⟩ *)
Lemma inv_stab:
  forall {n: nat} (pstr: PauliElement n) (ψ:  Vector (2^n)),
  WF_Matrix ψ -> stab pstr ψ -> stab (pstr^-1) ψ.
Proof.
  intros n pstr ψ Hwf Hstab.
  unfold stab in *.
  rewrite <- Hstab at 1.
  rewrite /act_n /applyP /=.
  rewrite <- Mmult_assoc.
  (* Search int_pn "×". *)
  rewrite int_pn_Mmult.
  change mul_pn with (@mulg (PauliElement n)).
  rewrite mulVg /=.
  apply one_stab_everything; easy.
Qed.

Close Scope group_scope.

Print Vector.

Ltac unfold_stab := 
rewrite /stab /act_n /applyP /=.



(* 
If we take the tensor product of a two states, with stabiliser groups A and B (respectively), then the resulting tensor product state has stabiliser group given by the cartesian product A × B. 
*)
Theorem stab_compose:
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  let cpstring := concate_pn pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stab  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  by rewrite H1 H2;
  reflexivity.
  all: try by rewrite - Nat.pow_add_r.
Qed.
  
(* The vector space of EPR Pair can be defined by generator <XX, ZZ> *)
Fact bell_stabilizer: 
  (One, [p X,X]) ∝1 ∣Φ+⟩ /\ (One, [p Z,Z]) ∝1 ∣Φ+⟩.
Proof.
  split.
  - unfold stab.
    lma'.
    unfold_stab.
    simpl;Qsimpl.
    auto with wf_db. 
  - unfold stab.
    lma'.
    unfold_stab.
    simpl;Qsimpl.
    auto with wf_db.
Qed. 

Fact three_qubit_state_stabilizer:
  (One, [p Z, Z, I]) ∝1 ∣000⟩ /\ (One, [p Z, Z, I]) ∝1 ∣000⟩.
Proof.
  split.
  - unfold_stab; Qsimpl.
    solve_matrix.
  - unfold_stab; Qsimpl.
    solve_matrix.
Qed.

Theorem stab_closed: 
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  mulg pstr1 pstr2 ∝1 ψ
.
Proof.
  unfold_stab => n pstr1 pstr2 psi H0 H1.
  rewrite -int_pn_Mmult.
  by rewrite Mmult_assoc H1 H0.
Qed.

Import Commutativity.


(* there is no -1 in any stabilizer group *)
Theorem stab_group_no_m1: 
  forall {n: nat} (pstr1 pstr2: PauliElement n) (ψ:  Vector (2^n)),
  pstr1 ∝1 ψ ->
  pstr2 ∝1 ψ ->
  WF_Matrix ψ ->
  ψ <> Zero ->
  mulg pstr1 pstr2 <> (NOne, id_pn n).
Proof.
  unfold not.
  intros.
  assert ((NOne, id_pn n) ∝1 ψ) as H4.
  {
    rewrite <- H3.
    apply stab_closed; easy.
  }
  contradict H4.
  move: (one_stab_everything ψ H1).
  unfold_stab; Qsimpl => Hid.
  rewrite Mscale_mult_dist_l Hid.
  apply negate_change_state.
  unfold not. intros.
  by apply H2. 
Qed.

Require Import ExtraSpecs.



(* TODO This is not so efficient *)
(* Try using seq.take and drop  *)
Theorem stab_compose_alt:
  forall {n m: nat} (pstr1: PauliElement n) (pstr2: PauliElement m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := concate_pn pstr1 pstr2 in
  pstr1 ∝1 ψ1 ->
  pstr2 ∝1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n m ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stab  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  by rewrite H1 H2;
  reflexivity.
  all: try by rewrite - Nat.pow_add_r.
Qed.



Lemma stab_addition:
  forall {n: nat} (pstr: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  pstr ∝1 ψ1 ->
  pstr ∝1 ψ2 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  unfold_stab => n pstr psi1 psi2 H0 H1.
  (* Search (_ × (_ .+ _) ). *)
  rewrite Mmult_plus_distr_l.
  by rewrite H0 H1.
Qed.

Lemma stab_scale: 
  forall {n: nat} (pstr: PauliElement n) (ψ:  Vector (2^n)) (phase: C),
  pstr ∝1 ψ ->
  pstr ∝1 (phase .* ψ).
Proof.
  move => n pstr psi s.
  unfold_stab.
  rewrite Mscale_mult_dist_r.
  by move => ->.
Qed.

Lemma stab_cons:
  forall {n: nat} (pstr: PauliString n) (hp: PauliBase) (hv: Vector 2) (tv:  Vector (2^n)),
  pstr ∝1 tv ->
  stab_1 hp hv ->
  (One, [tuple of hp::pstr]) ∝1 (hv ⊗ tv).
Proof.
  move => n pstr hp hv tv.
  unfold_stab.
  Qsimpl.
  rewrite theadCons beheadCons.
  rewrite kron_mixed_product'; try auto.
  rewrite /stab_1 /act_1 /= /apply1p /=; Qsimpl.
  move => H1 H2.
  rewrite H2.
  apply kron_simplify; auto.
Qed.

Ltac normalize_kron_notation :=
  repeat rewrite <- kron_assoc by auto 8 with wf_db;
  try easy.

Fact stab_04_fact:
  (One, [p Z, I, I, I]) ∝1 ∣0,0,0,0⟩.
Proof.
  replace ∣0,0,0,0⟩ with (∣0,0⟩ ⊗ ∣0,0⟩) by normalize_kron_notation.
  apply (stab_compose ([p1 Z, I]) ([p1 I, I])).
  all: unfold stab; simpl; Qsimpl; lma'; apply apply_n_wf.
  all: auto with wf_db.
Qed.

Definition shor_code_0 := (3 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)).

Ltac by_compose_stab s1 s2 :=
  apply (stab_compose_alt s1 s2); Qsimpl;
  (unfold stab; simpl; Qsimpl; lma');
  apply apply_n_wf; auto with wf_db.

(* Sing part of shor's code  *)
Lemma shor_code_part_stab:
  [p1 Z, Z, I] ∝1 (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  apply stab_addition.
  by_compose_stab ([p1 Z, Z]) ([p1 I]).
  by_compose_stab ([p1 Z, Z]) ([p1 I]).
Qed.

(* basically the same as the original *)
(* but it is more efficient in computing *)
Theorem stab_compose_alt':
  forall {n m: nat} 
    (substr1: PauliElement n) (substr2: PauliElement m) (pstr: PauliElement (n + m))
    (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
    (pstr = concate_pn substr1 substr2) ->
   substr1 ∝1 ψ1 -> substr2 ∝1 ψ2 -> pstr ∝1 (ψ1 ⊗ ψ2).
Proof. move => *. by subst; apply stab_compose_alt. Qed.


(* Solves goals like [p ... ] = concate_pn [p ...] [p ...]  *)
Ltac by_compose_pstring :=
    rewrite /concate_pn /mulg /=;
    apply injective_projections; simpl;
    [by easy | by apply /eqP].


(* Solve goals like [p1 I ...] = id_png n *)
Ltac by_unify_ids :=
  rewrite /id_png;
  apply injective_projections; 
  [by easy | rewrite /id_pn /=; by apply /eqP]. 
  

Set Default Timeout 5.

Goal [p1 Z, Z, I, I, I, I] ∝1 ∣ 0, 0, 0, 1, 1, 1⟩.
Proof.
  (* this is theoritical not necessary, *)
  (* but without it coq will hanging *)
  replace ∣ 0, 0, 0, 1, 1, 1⟩ with (∣ 0, 0⟩ ⊗ ∣0, 1, 1, 1⟩) by normalize_kron_notation .
  apply (stab_compose_alt'([p1 Z, Z]) ([p1 I, I, I, I])).
  by_compose_pstring. 
  apply (stab_compose_alt' ([p1 Z ]) ([p1 Z])). by_compose_pstring.
  all: auto with stab_db.
  replace ([ p1 I, I, I, I]) with (id_png 4) by by_unify_ids.
  apply one_stab_everything. 
  auto with wf_db.
Qed.

(* solve goals like [p1 I ...] ∝1 ∣... ⟩ *)
Ltac by_id_stab n :=
  match goal with
  | [ |- (?pstr ∝1 _) ] =>
    replace pstr with (id_png n) by by_unify_ids;
    apply one_stab_everything;
    auto with wf_db
  end.

Lemma shor_code_stab: [p1 Z, Z, I, I, I, I, I, I, I] ∝1 shor_code_0.
Proof.
  rewrite /shor_code_0.
  rewrite /kron_n kron_1_l.
  apply (stab_compose_alt' ([p1 Z, Z, I, I, I, I]) ([p1 I, I, I])). 
    by_compose_pstring.
  apply (stab_compose_alt' ([p1 Z, Z, I]) ([p1 I, I, I])).
    by_compose_pstring.
  apply shor_code_part_stab.
  all: try (by_id_stab 3%nat).
  auto with wf_db.
Qed.

(* 
This section introduces additional properties and lemmas related to stabilizers.
It defines the concept of "flip_sign" (anti-stabilizer) and provides examples and theorems 
demonstrating how stabilizers and anti-stabilizers interact under operations like tensor products.
Key results include the combination of two anti-stabilizers into a stabilizer and 
the symmetry of stabilizers under certain transformations. *)
(* Section MoreProps. *)

(* aka anti-stabilizer *)
Definition flip_sign {n: nat} (pstring: PauliElement n) (psi: Vector (2^n)) :=
  act_n n psi pstring = -1 .* psi.

(* A fancy symbol for "stabilize" *)
Notation "pstring ∝-1 ψ" := (flip_sign pstring ψ) (at level 50).

Example z1_f:
  [ p1 Z ] ∝-1  ∣ 1 ⟩.
Proof. by simpl_stabn. Qed.

From QuantumLib Require Import Complex.
(* two anti-stabilizers combine into a stabilizer under the tensor product *)
Theorem stab_even_slign_flip:
  forall {n m: nat} (pstr1: PauliElement n) (pstr2: PauliElement m) (ψ1:  Vector (2^n)) (ψ2:  Vector (2^m)),
  let cpstring := concate_pn pstr1 pstr2 in
  pstr1 ∝-1 ψ1 ->
  pstr2 ∝-1 ψ2 ->
  cpstring ∝1 (ψ1 ⊗ ψ2).
Proof.
  move => n m ps1 ps2 psi1 psi2.
  move: (compose_pstring_correct ps1 ps2).
  unfold_stab  => H0 H1 H2.
  restore_dims.
  rewrite H0.
  rewrite kron_mixed_product'; try by auto.
  move: H1 H2. rewrite /flip_sign /act_n /= /applyP => H1 H2.
  rewrite H1 H2 Mscale_kron_dist_r.
  restore_dims. 
  rewrite Mscale_kron_dist_l.
  rewrite Mscale_assoc.
  replace (-1 * -1) with (C1) by lca.
  by Qsimpl.
  all: try by rewrite - Nat.pow_add_r.
Qed.

Import all_pauligroup.

Definition ZZ := ([p1 Z, Z]) : PauliElement 2.

Example stab_z11:
  ([ p1 Z, Z]) ∝1 ∣ 1, 1 ⟩.
Proof.
  apply (stab_even_slign_flip ([p1 Z]) ( [p1 Z])).
  by simpl_stabn.
  by simpl_stabn.
Qed.

Theorem stab_symm_perm:
  forall {n: nat} (pstr: PauliElement n) (ψ1 ψ2:  Vector (2^n)),
  act_n n ψ1 pstr =  ψ2 ->
  act_n n ψ2 pstr =  ψ1 ->
  pstr ∝1 (ψ1 .+ ψ2).
Proof.
  unfold_stab => n pstr psi1 psi2 H0 H1.
  rewrite /stab /act_n /= /applyP /=.
  rewrite Mmult_plus_distr_l.
  rewrite H0 H1.
  by rewrite Mplus_comm.
Qed.
  
  
(* Cannot do this because quantumlib do not provide a computable process *)
(* of Mmult *)
Fail Definition stab_s {n: nat} (psi: Vector (2^n)) :=
  [set x | stab x psi].

(* Instead, we can define using Coq subtype  *)
Definition stab_s {n: nat} (psi: Vector (2^n)) := { 
  op: PauliElement n | op ∝1 psi \/ exists (a b:PauliElement n), a ∝1 psi /\ b ∝1 psi /\ op = mulg a b 
}.

Theorem stab_s_correct n:
  forall (psi: Vector (2^n)) (gen: stab_s psi),
    `gen ∝1 psi.
Proof.
  move => psi [op [Hop1 | Hop2]].
  - apply Hop1.
  - move: Hop2 => [a [b H]].
    move: H => [Ha [Hb Hc]].
    subst. simpl.
    by apply stab_closed.
Qed.

Open  Scope group_scope.
(* an n-qubit stabilizer group is any subgroup of P^n that is 
abelian (commutative) and dos not contain -1  *)
Definition is_stab_set {n} (S: { set PauliElement n }) :=
  forall a b, a \in <<S>> -> b \in <<S>> -> mulg a b = mulg b a /\ 
  ~~ (minus_id_png n \in << S >>).

Definition is_stab_set_spec {n} (S: {set PauliElement n}) (v: Vector (2^n)):=
  forall x, x \in << S >> -> x ∝1 v.

(* The weight of a stabilizer group is the number of qubits that are not I *)
(* in the stabilizer group *)
Definition weight {n} (pt: PauliString n): nat := 
  count (fun x => x != I) pt.

Goal weight ([p Z, Z, I]) = 2%nat.
Proof.
  by rewrite /weight.
Qed.

(* Describe the error detection ability *)
Section Syndrome.

(* The number of physical qubits *)
Variable n: nat.
(* The generator set *)
Variable g: {set PauliElement n}.
Hypothesis H: is_stab_set g.

Definition with_1 (pt: PauliString n): PauliElement n := (One, pt).

(* an detectable error is an error that  *)
(* note that we usually require the phase of error operator to be 1 *)
(* Otherwise, it will be Z (negate phase) *)
Definition detectable (E: PauliString n) := 
  exists (pstr: PauliElement n), pstr \in g /\ 
  (mulg pstr (with_1 E) != mulg (with_1 E) pstr).


(* The dimension of the code space 
, which is typically, the numbef of physical qubits - number of independent generator *)
(* A future work is to prove this holds in principle *)
Definition dimension := subn n #|g|.

(* the distance of a generator = weight(E)  *)
(* where E is an error and E cannot be detected *)
Definition distance_spec (E: PauliString n) (d: nat) :=
  not (detectable E) /\ weight E = d.

(* The distance of a code is the minimal weight of an undetectable error *)
Definition distance (d: nat):= 
  exists (E: PauliString n), distance_spec E d /\
    forall (E': PauliString n) d', distance_spec E' d' -> leq d d'.

(* A sound difinition of distance, which does not require to show 
  the error is the minimum in the whole world  
*)
Definition distance_s (d: nat):= 
  exists (E: PauliString n), distance_spec E d.
  

(* These definitions are very axiomatic and not verified from principle *)
(* It's nice if we can verify their physical meanning *)
(* Prove that detectable is correct *)
End Syndrome.

Lemma int_pnb_apply_cons:
  forall {n} (p: PauliBase) (operator: PauliOperator n)  
    (head: Vector 2) (tail: Vector (2^(n))),
  (* A ⊗ B *)
  int_pnb ([tuple of p::operator]) × (head ⊗ tail) = 
  ((int_p1b p) × head) ⊗ ((int_pnb operator) × tail).
Proof.
  move => n p pt vh vt.
  rewrite PauliProps.int_pnb_cons.
  by rewrite kron_mixed_product.
Qed.
