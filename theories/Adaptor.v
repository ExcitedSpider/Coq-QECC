Require Import PauliProps.
From mathcomp Require Import ssrfun fingroup eqtype tuple seq fintype.

Require Import PauliGroup.
Import P1BaseGroup.
Import P1Group.
Import PNBaseGroup.
Import PNGroup.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Module Pauli.

(* PauliOperator directly from group definition *)
Check PauliBase.

Check phase.

(* PauliBase with phase *)
Check PauliElem1.

Definition p1g_of (s: phase) (op: PauliBase): PauliElem1:=
  pair s op.

(* Define a custom notation for elements of the Pauli group *)
Notation "s · p" := (p1g_of s p) 
  (at level 40, left associativity).

Check One · X: PauliElem1.
Check Img · Z: PauliElem1.

Lemma pauli_eq_comp:
forall sa pa sb pb,
sa = sb -> pa = pb -> sa · pa = sb · pb.
Proof.
intros.
subst.
reflexivity.
Qed.

Definition scalar_to_complex: phase -> C := int_phase.

(* use the interpretation function in group definition *)
Definition op_to_matrix: PauliBase -> Square 2 := int_p1b.

Definition pauli_to_matrix: PauliElem1 -> Square 2 := int_p1.

Example negY: pauli_to_matrix (NOne · Y) = -C1 .* σy.
Proof. reflexivity. Qed.

Example negIX: pauli_to_matrix (NImg · X) = -Ci .* σx.
Proof. reflexivity. Qed.

Lemma pauli_to_matrix_determinsitic: forall a b c,
pauli_to_matrix a = b ->
pauli_to_matrix a = c ->
b = c.
Proof.
intros.
subst.
reflexivity.
Qed.


Check Matrix.I 2.

Lemma square_2_eq_semantics : forall a b: Square 2,
a = b ->
a 0%nat 0%nat = b 0%nat 0%nat /\
a 0%nat 1%nat = b 0%nat 1%nat /\ 
a 1%nat 0%nat = b 1%nat 0%nat /\
a 1%nat 1%nat = b 1%nat 1%nat.
Proof.
intros.
subst.
repeat (split).
Qed.

Close Scope group_scope.

Example one_semantics:
Matrix.I 2 0%nat 0%nat = 1.
Proof.
unfold Matrix.I.
simpl.
reflexivity.
Qed.

Open Scope C_scope.
(* 
Transform 
(C1 .* Matrix.I 2) 0%nat 0%nat = (C1 .* σx) 0%nat 0%nat
to 
C1 * (Matrix.I 2 0%nat 0%nat) = ...
*)

Lemma scalar_asso_mapply:
forall (c: C) (m: Square 2) (i j: nat),
Nat.lt i 2%nat -> 
Nat.lt j 2%nat ->
(c .* m) i j = c * (m i j).
Proof.
unfold scale.
reflexivity.
Qed.  

Ltac contradict_c_eq H :=
field_simplify_eq in H;
inversion H as [HC];
contradict HC;
lra.

Lemma pauli_matrix_no_overlap : forall sa sb pa pb,
pauli_to_matrix (sa · pa) = pauli_to_matrix (sb · pb) ->
pa <> pb \/ sa <> sb ->
False.
Proof.
intros.
destruct H0.
{
  apply H0; clear H0.     
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: try(
    apply square_2_eq_semantics in H;
    simpl in H;
    unfold Matrix.I, σx, σz, σy in H;
    destruct H as [H0 [H1 [H2 H3]]];
    repeat (rewrite scalar_asso_mapply in H0, H1, H2, H3 by lia);
    simpl in H0, H1, H2, H3
  ).
  all: try(contradict_c_eq H0).
  all: try(contradict_c_eq H1).
  all: try(contradict_c_eq H2).
  all: try(contradict_c_eq H3).
}
{
  apply H0; clear H0.     
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: try(
    apply square_2_eq_semantics in H;
    simpl in H;
    unfold Matrix.I, σx, σz, σy in H;
    destruct H as [H0 [H1 [H2 H3]]];
    repeat (rewrite scalar_asso_mapply in H0, H1, H2, H3 by lia);
    simpl in H0, H1, H2, H3
  ).
  all: try(contradict_c_eq H0).
  all: try(contradict_c_eq H1).
  all: try(contradict_c_eq H2).
  all: try(contradict_c_eq H3).
}
Qed.

Lemma pauli_to_matrix_comp: forall sa pa sb pb,
pauli_to_matrix (sa · pa) = pauli_to_matrix (sb · pb) ->
sa = sb /\ pa = pb.
Proof.
intros.
split.
{
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: exfalso; eapply pauli_matrix_no_overlap ; try(apply H); 
    try(left; discriminate);
    try(right;discriminate).
}
{
  destruct sa, sb, pa, pb.
  all: try(reflexivity).
  all: exfalso; eapply pauli_matrix_no_overlap ; try(apply H); 
    try(left; discriminate);
    try(right;discriminate).
}
Qed.


Lemma pauli_to_matrix_injective: forall a b,
pauli_to_matrix a = pauli_to_matrix b <-> a = b.
Proof.
split.
{ 
  intros.
  destruct a, b.
  apply pauli_to_matrix_comp in H.
  destruct H.
  subst.
  reflexivity.
}
{
  intros.
  subst.
  reflexivity.
}
Qed.

(* The operation on the PauliElem1 group *)
(* Define the operation as relation makes it so hard *)
Inductive pmultrel: PauliElem1 -> PauliElem1 -> PauliElem1 -> Prop := 
| PauliMultRel: forall (a b c: PauliElem1),
  (pauli_to_matrix a) × (pauli_to_matrix b) = pauli_to_matrix c ->
  pmultrel a b c.

Example fact_square_x: 
pmultrel (One · X)  (One · X) (One · I).
Proof.
apply PauliMultRel.
simpl.
solve_matrix.
Qed.

(* Definition id_p1 := (One · I). *)
Definition id := id_p1.

Lemma pauli_op_wf: 
forall (a: PauliElem1), WF_Matrix (pauli_to_matrix a).
Proof.
intros.
destruct a as [s p].
destruct s, p;
simpl;
auto with wf_db.
Qed.

Definition inverse_op: PauliBase -> PauliBase := inv_p1b.

Definition inverse_scalar: phase -> phase := inv_phase.


Definition pinv := inv_p1.

Lemma pinv_correct:
forall (a: PauliElem1), exists (a': PauliElem1),
  pmultrel a a' id_p1.
Proof.
intros.
exists (pinv a). 
apply PauliMultRel. 
destruct a as [s p].
destruct s, p;
solve_matrix.
Qed.

Lemma scalar_closure:
forall a b,
exists (c: phase), 
  (scalar_to_complex a) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
intros.
destruct a, b.
all: simpl.
all: try (exists One; simpl; lca).
all: try (exists Img; simpl; lca).
all: try (exists NOne; simpl; lca).
all: try (exists NImg; simpl; lca).
Qed.

Ltac MRefl :=
simpl; Qsimpl; try reflexivity; try solve_matrix.

Ltac MReflExists scale op :=
try (exists op, scale; MRefl).


Lemma op_closure:
forall a b,
exists (c: PauliBase) (s: phase), 
  (op_to_matrix a) × (op_to_matrix b) = (scalar_to_complex s) .* (op_to_matrix c).
Proof.
intros a b.
destruct a, b.
all: simpl; Qsimpl.
(* This is so painful. don't know how to revert `exists` *)
MReflExists One I.
MReflExists One X.
MReflExists One Y.
MReflExists One Z.
MReflExists One X.
MReflExists One I.
MReflExists Img Z.
MReflExists NImg Y.
MReflExists One Y.
MReflExists NImg Z.
MReflExists One I.
MReflExists Img X.
MReflExists One Z.
MReflExists Img Y.
MReflExists NImg X.
MReflExists One I.
Qed.


(* This one succeed by using two lemmas *)
Lemma pauli_closure':
forall a b,
exists (c: PauliElem1), pmultrel a b c.
Proof.
intros a b.
destruct a as [sa pa], b as [sb pb].
specialize (scalar_closure sa sb) as [sc Hsc].
specialize (op_closure pa pb) as [pc Hpc].
destruct Hpc as [s Hpc].
specialize (scalar_closure sc s) as [sc' Hsc'].
exists (pair sc' pc).
apply PauliMultRel; simpl.
(* Search (_ × (_ .* _)). *)
repeat rewrite Mscale_mult_dist_r.
(* Search (_ .* (_ × _)). *)
rewrite Mscale_mult_dist_l.
replace op_to_matrix  with int_p1b in Hpc by easy. 
rewrite Hpc.
rewrite Mscale_assoc.
replace scalar_to_complex with int_phase  in Hsc' by easy. 
rewrite <- Hsc'.
(* Search ((_ * _) = (_ * _)). *)
rewrite Cmult_comm.
replace scalar_to_complex  with int_phase in Hsc by easy.
rewrite Hsc.
rewrite Mscale_assoc.
reflexivity.
Qed.

Lemma pmultrel_assoc : forall a b ab c abc : PauliElem1,
pmultrel a b ab ->
pmultrel ab c abc ->
exists bc, pmultrel b c bc /\ pmultrel a bc abc.
Proof.
intros a b ab c abc HL HR.
specialize (pauli_closure' b c) as Hbc.
destruct Hbc as [bc Hbc].
exists bc.
split.
- assumption.
- apply PauliMultRel.
  inversion Hbc; subst.
  rewrite <- H; clear H Hbc.
  inversion HR; subst.
  rewrite <- H; clear H HR.
  inversion HL; subst.
  rewrite <- H; clear H HL.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.


(* 
=======================================================
Define pmultrel as a function

We found reasoing pmultrel as a relation is tiresome.
So it is better that we define it as a function.
Fortunately, as we have proved many facts about pmultrel,
it will be much easier now.
=======================================================
*)

Definition op_prod_op := mul_p1b.


Definition op_prod_s := rel_phase.


Definition op_prod (a b: PauliBase): (phase * PauliBase) := 
  (rel_phase a b, mul_p1b a b).

Definition op_prod_alt(a b: PauliBase): (phase * PauliBase) := 
    ( op_prod_s a b, op_prod_op a b).

Lemma op_prod_alt_correct: 
forall a b,
op_prod_alt a b = op_prod a b.
Proof.
  intros.
  destruct a, b; easy.
Qed.



Definition s_prod := mul_phase.

Lemma inverse_scalar_correct:
  forall sc, s_prod sc (inverse_scalar sc) = One
. 
intros.
destruct sc; easy.
Qed.

Lemma s_prod_total:
  forall s1 s2,
  exists s3,
  s_prod s1 s2 = s3.
Proof.
  intros.
  destruct s1, s2.
  all: simpl.
  all: try(exists One; reflexivity).
  all: try(exists Img ; reflexivity).
  all: try(exists NOne  ; reflexivity).
  all: try(exists NImg  ; reflexivity).
Qed.

Definition combined_scalars (s1 s2 s3: phase) : phase := 
s_prod s1 (s_prod s2 s3).

Lemma combined_scalars_total:
  forall s1 s2 s3,
  exists s4,
  combined_scalars s1 s2 s3 = s4.
Proof.
  intros.
  unfold combined_scalars.
  apply s_prod_total.
Qed.

Definition pmul (a b: PauliElem1): PauliElem1 := 
match a, b with
| pair sa pa, pair sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    let combined_scalar := combined_scalars sab sa sb in
    pair combined_scalar pab
end.

Lemma s_prod_identity:
  forall s, s_prod s One = s.
Proof.
  intros.
  destruct s.
  all: simpl; reflexivity.
Qed.

Lemma s_prod_correct:
  forall s0 s1,
  scalar_to_complex (s_prod s0 s1) = scalar_to_complex s0 * scalar_to_complex s1.
Proof.
  intros.
  destruct s0, s1.
  all: simpl; lca.
Qed.

Lemma combinded_scalars_correct:
  forall s0 s1 s2,
  scalar_to_complex (combined_scalars s0 s1 s2) = 
    scalar_to_complex s0 *
    scalar_to_complex s1 *
    scalar_to_complex s2.
Proof.
  intros.
  unfold combined_scalars.
  repeat rewrite s_prod_correct.
  lca.
Qed.

Lemma op_prod_total:
  forall op1 op2,
  exists prod_s prod_op,
  op_prod op1 op2 = (prod_s, prod_op).
Proof.
  intros.
  remember (op_prod op1 op2).
  destruct p as [s p].
  exists s, p.
  reflexivity.
Qed.

Lemma op_prod_correct:
  forall op1 op2,
  exists prod_s prod_op,
  op_prod op1 op2 = (prod_s, prod_op) /\
  (op_to_matrix op1) × (op_to_matrix op2) = (scalar_to_complex prod_s) .* (op_to_matrix prod_op).
Proof. 
  intros.
  specialize (op_prod_total op1 op2) as [s [p H]].
  exists s, p.
  split.
  - assumption.
  - unfold scalar_to_complex. 
    destruct op1, op2.
    all: simpl in H; inversion H; subst.
    all: simpl; Qsimpl.
    all: try(reflexivity).
    all: solve_matrix. (* these facts can be lemmas? *) 
Qed.



Lemma pmul_is_Mmult:
forall a b, pauli_to_matrix (pmul a b) = 
  (pauli_to_matrix a) × (pauli_to_matrix b).
Proof.
  intros.
  destruct a as [s p], b as [s0 p0].
  specialize (op_prod_correct p p0) as [s_prod [op_prod [Heq H]]].
  unfold pmul.
  rewrite Heq.
  unfold pauli_to_matrix .
  replace op_to_matrix with int_p1b in H by easy. 
  replace scalar_to_complex with int_phase in H by easy.
  unfold int_p1.
  distribute_scale. 
  rewrite H.
  rewrite Mscale_assoc.
  rewrite combinded_scalars_correct.
  assert (scalar_to_complex s_prod * scalar_to_complex s * scalar_to_complex s0 = scalar_to_complex s * scalar_to_complex s0 * scalar_to_complex s_prod) by lca.
  rewrite H0.
  reflexivity.
Qed.


Definition apply_s (s: phase) (p: PauliElem1): PauliElem1 :=
match p with
  | pair s0 op => pair (s_prod s s0) op
end.

Definition pneg (p: PauliElem1): PauliElem1 := apply_s (NOne) p.

Definition pmul_alt (a b: PauliElem1): PauliElem1 := 
match a, b with
| pair sa pa, pair sb pb => 
    let (sab, pab) := (op_prod pa pb) in
    (* let combined_scalar := combined_scalars sab sa sb in *)
    apply_s sab (pair (s_prod sa sb) pab)
end.

Lemma pmul_alt_correct:
forall a b,
pmul_alt a b = pmul a b.
Proof.
intros.
destruct a as [s p], b as [s0 p0].
simpl.
destruct s, s0.
all: simpl.
all: destruct p, p0.
all: simpl.
all: reflexivity.
Qed. 

(* verify our function version of pmultrel is correct *)
Lemma pmul_correct_r: forall (a b c: PauliElem1),
(pmul a b) = c -> pmultrel a b c. 
Proof.
intros.
subst.
destruct a as [s p], b as [s0 p0].
destruct s, p, s0, p0.
all:  simpl; apply PauliMultRel; simpl; Qsimpl.
(* this is not necessary but slightly improve performance *)
all: try (rewrite Mscale_mult_dist_r). 
all: try(Qsimpl; try(reflexivity)).
all: try(rewrite Mmult_1_l).
all: try (Qsimpl; autorewrite with Q_db).
(* tried of finding patterns. *)
all: try(solve_matrix).
Qed.

Lemma pmul_correct_l: forall (a b c: PauliElem1),
pmultrel a b c -> (pmul a b) = c. 
Proof.
intros.
inversion H; subst.
rewrite <- pmul_is_Mmult in H0.
rewrite pauli_to_matrix_injective in H0.
assumption.
Qed.

Theorem pmul_prod_eq: forall (a b c: PauliElem1),
pmultrel a b c <-> (pmul a b) = c. 
Proof.
split.
apply pmul_correct_l.
apply pmul_correct_r.
Qed.

(* 
The commute / anticommute are two very important properties in stabilizer formalism. we want to show that phase does not affect commute / anticommute relation.
We also hope to inspect how our new defined prod function can simplify the proof.
*)

Inductive commute: PauliElem1 -> PauliElem1 -> Prop :=
| CommuteRel: forall (pa pb: PauliElem1),
  (pmul pa pb) = (pmul pb pa) -> commute pa pb.

Lemma commute_self:
forall (p: PauliElem1), commute p p.
Proof.
intros.
apply CommuteRel. reflexivity.
Qed.

Lemma commute_identity:
forall (p: PauliElem1), commute p id_p1.
Proof.
intros.
apply CommuteRel.
simpl.
(* no need to work on relations anymore! 
   just destruct everything and let coq do the calculation.
*)
destruct p.
destruct p.
all: destruct p0.
all: try(reflexivity).
Qed.

(* Can you think a better name *)
Lemma scalar_does_not_affect_commute:
forall p1 p2 s1 s2, commute (One · p1) (One · p2) ->
commute (s1 · p1) (s2 · p2).
Proof.
intros.
inversion H; subst.
apply CommuteRel.
simpl.
unfold combined_scalars.
destruct s1, s2, p1, p2.
(* some can be resolved by performing multiplication *)
all: try (reflexivity).
(* some can be resolved by contradiction *)
all: try (inversion H0).
Qed.

(* 
TODO: Replace this with ExtraSpecs
the definition has a slight issue: it depends on how `apply_s` is defiend. Although `apply_s` is straightforward, but it is not certified. 
*)
Inductive anticommute: PauliElem1 -> PauliElem1 -> Prop :=
| AnticommuteRel: forall (pa pb: PauliElem1),
  (pmul pa pb) = apply_s (NOne) (pmul pb pa) -> anticommute pa pb.

Example anticommute_exp0:
anticommute (One · X) (One · Y).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

Example anticommute_exp1:
anticommute (One · Y) (One · Z).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

Example anticommute_exp2:
anticommute (One · X) (One · Z).
Proof.
apply AnticommuteRel.
reflexivity.
Qed.

(* 
very similar to `scalar_does_not_affect_commute`
I wonder if there is a way to extract the same pattern
*)
Lemma scalar_does_not_affect_anticommute:
forall p1 p2 s1 s2, anticommute (One · p1) (One · p2) ->
anticommute (s1 · p1) (s2 · p2).
Proof.
intros.
inversion H; subst.
apply AnticommuteRel.
simpl.
unfold combined_scalars.
destruct s1, s2, p1, p2.
(* some can be resolved by performing multiplication *)
all: try (reflexivity).
(* some can be resolved by contradiction *)
all: try (inversion H0).
Qed.

(* 
At this point, it is guranteed that scalars do not affect us
to reasoing about (anti)commute. so we can throw them away.
*)

Example anticommute_exp3:
anticommute (NImg · X) (Img · Z).
Proof.
apply scalar_does_not_affect_anticommute.
apply AnticommuteRel.
reflexivity.
Qed.

(* It seems that the proof of anticommute_exp3 is pretty mechanical.
we can work on some automation later. 
*)

Example ix_ineq: Matrix.I 2 <> σx.
Proof.
  unfold not.
  intros H.
  assert (Hcontra: Matrix.I 2 0%nat 0%nat = σx 0%nat 0%nat).
  { rewrite H. reflexivity. }
  unfold Matrix.I in Hcontra.
  simpl in Hcontra.
  inversion Hcontra.
  contradict H1.
  lra.
Qed.

Example iy_ineq: Matrix.I 2 <> σy.
Proof.
  unfold not.
  intros H.
  assert (Hcontra: Matrix.I 2 0%nat 0%nat = σy 0%nat 0%nat).
  { rewrite H. reflexivity. }
  unfold Matrix.I in Hcontra.
  simpl in Hcontra.
  inversion Hcontra.
  contradict H1.
  lra.
Qed.


(* Additonal Lemmas *)

Lemma inverse_op_correct:
  left_inverse I inverse_op op_prod_op.
Proof.
  unfold left_inverse.
  intros.
  destruct x; reflexivity.
Qed.

Lemma s_prod_comm:
  commutative s_prod.
Proof.
  unfold commutative.
  intros.
  now destruct x, y; simpl.
Qed.

Lemma s_prod_left_id: left_id One s_prod.
Proof.
  unfold left_id.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma s_prod_right_id: right_id One s_prod.
Proof.
  unfold right_id.
  intros.
  simpl.
  destruct x; easy.
Qed.

Lemma op_prod_snd_assoc:
  forall a b c, 
  (op_prod a (op_prod b c).2).2 = (op_prod (op_prod a b).2 c).2.
Proof.
  intros.
  simpl.
  destruct a, b, c.
  all: simpl; reflexivity.
Qed.

Lemma op_prod_snd_helper:
  forall a b s p,
  (s, p) = op_prod a b ->
  p =  (op_prod a b).2.
Proof.
  intros.
  inversion H.
  simpl.
  reflexivity.
Qed.

End Pauli.

Module PauliString.
Import Pauli.
Definition PauliVector n := Vector.t PauliBase n.
Definition PVector0 := Vector.nil PauliBase.

Fixpoint pvmul {n: nat} (a b : PauliVector n) : phase * PauliVector n :=
  (* Looks like dark magic *)
  match a in Vector.t _ n return Vector.t _ n -> phase * PauliVector n  with 
  | ha :: ta => fun b => 
    let hb := Vector.hd b in
    let tb := Vector.tl b in 
    let (stl, ptl) := pvmul ta tb in
    let (sh, ph) := op_prod ha hb in
    (s_prod stl sh, ph::ptl)
  | [] => fun _ => (One, [])
  end b.

Fixpoint pvmul_v {n: nat} (a b : PauliVector n) : PauliVector n :=
  match a in Vector.t _ n return Vector.t _ n -> PauliVector n  with 
  | ha :: ta => fun b => 
    let hb := Vector.hd b in
    let tb := Vector.tl b in 
    let ptl := pvmul_v ta tb in
    let ph := op_prod_op ha hb in
    ph::ptl
  | [] => fun _ => []
  end b.

Fixpoint pvmul_s {n: nat} (a b : PauliVector n) : phase  :=
    (* Looks like dark magic *)
    match a in Vector.t _ n return Vector.t _ n -> phase with 
    | ha :: ta => fun b => 
      let hb := Vector.hd b in
      let tb := Vector.tl b in 
      let stl := pvmul_s ta tb in
      let sh := op_prod_s ha hb in
      s_prod stl sh
    | [] => fun _ => One
    end b.

(* Easier to use in verification *)
Definition pvmul_alt  {n: nat} (a b : PauliVector n) : phase * PauliVector n 
  := (pvmul_s a b, pvmul_v a b).

Lemma pvmul_alt_correct: 
  forall n (pa pb: PauliVector n),
  pvmul_alt pa pb = pvmul pa pb.
Proof.
  intros.
  induction n.
  - dependent destruction pa.
    dependent destruction pb.
    unfold pvmul_alt.
    simpl.
    reflexivity.
  - dependent destruction pa.
    dependent destruction pb.
    specialize (IHn pa pb).
    simpl.
    unfold pvmul_alt in IHn.
    rewrite <- IHn.
    unfold pvmul_alt; simpl.
    simpl.
    f_equal.
Qed.

Example pstring_prod_exp: 
  pvmul (Z::X::X::I::[]) (X::X::Y::Y::[]) = (NOne, (Y::I::Z::Y::[])).
Proof.
  simpl.
  reflexivity.
Qed.

(* The Pauli String *)
Definition PString (n : nat) : Set := phase * PauliVector n.

(* [X;Y;Z] has been occupied by QuantumLib *)
(* We defined a new annotation here Use a prefix `p` to avoid mess up *)
(* TODO: Maybe I should use a scope for this *)

Notation "p[ x , y , .. , z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) (at level 60).

Notation "p[ x ]" := (x :: []) (at level 60).

Definition pstring_example0 : PString 3 :=
  (One, p[X, Y, Z]).

(* `::` is interpreted correctly *)
Definition pstring_example1 : PString 3 :=
  (One, X::Y::Z::[]).

Definition pstring_example2 : PString 0 :=
  (One, []).

Definition pstring_example3 : PString 1 :=
  (One, p[X]).

Definition psmul {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  let (sab, vab) := pvmul va vb in 
  ((combined_scalars sab sa sb), vab).

Definition apply_s {n: nat} (s: phase) (pstr: PString n): PString n :=
  let (s', pv) := pstr in
  (s_prod s s', pv).




(* Good !*)
Example pauli_calc0:
  psmul (One, (p[X,X,Y,Y])) (One, (p[Z,X,X,I]))
  = (NOne, (p[Y,I,Z,Y])).
Proof.
  simpl.
  reflexivity.
Qed.

Set Bullet Behavior "Strict Subproofs".
(* Simpler definition *)
Definition psmul_alt {n: nat} (a b: PString n) : PString n :=
  let (sa, va) := a in
  let (sb, vb) := b in
  ((combined_scalars (pvmul_s va vb)  sa sb), pvmul_v va vb).

Lemma psmul_alt_correct: 
  forall n (pa pb: PString n),
  psmul_alt pa pb = psmul pa pb.
Proof.
  intros n pa pb.
  induction n.
  - destruct pa as [s p], pb as [s0 p0].
    dependent destruction p.
    dependent destruction p0.
    unfold psmul_alt.
    simpl.
    reflexivity.
  - destruct pa as [s p], pb as [s0 p0].
    unfold psmul_alt.
    dependent destruction p.
    dependent destruction p0.
    specialize (IHn (s, p) (s0, p0)).
    simpl.
    specialize (pvmul_alt_correct _ p p0) as Hpvmul.
    unfold pvmul_alt in Hpvmul.
    rewrite <- Hpvmul.
    simpl.
    f_equal.
Qed.

(* Translate a PauliElem1 vector into a matrix *)
Fixpoint pvec_to_matrix {n:nat} (p: PauliVector n) : Square (2^n) :=
match p with
| [] => Matrix.I 1
| x::xs => (pauli_to_matrix (One, x)) ⊗ (pvec_to_matrix xs)
end.

Example pvec_interpret:
pvec_to_matrix (p[X,X,Y,Y]) = σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite <- kron_assoc by auto with wf_db.
  reflexivity.
Qed.

Definition pstr_to_matrix {n: nat} (pstr: PString n): Square (2^n) :=
let (s, pvec) := pstr in
(scalar_to_complex s) .* (pvec_to_matrix pvec).

Lemma pstr_to_matrix_WF n: 
  forall (pstr: PString n),
  WF_Matrix (pstr_to_matrix pstr).
Proof.
  intros.
  destruct pstr as [s p].
  simpl.
  apply WF_scale.
  dependent induction p.
  {
    simpl.
    auto with wf_db. 
  }
  {
    simpl.
    (* Search (_ .* _ ⊗ _).  *)
    rewrite Mscale_kron_dist_l.
    apply WF_scale.
    (* Search (WF_Matrix (_ ⊗ _)). *)
    apply WF_kron; try easy.
    destruct h; simpl; auto with wf_db. 
  }
Qed.


Example pstr_interpret:
pstr_to_matrix (NOne, (X::X::Y::Y::[])) = -C1 .* σx ⊗ σx ⊗ σy ⊗ σy.
Proof. 
  simpl.
  Qsimpl.
  repeat rewrite  kron_assoc by auto with wf_db.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.


Lemma length_0_vector:
  forall A (p: Vector.t A 0), p = [].
Proof.
  intros.
  dependent destruction p. (* regular destruct cannot handle this*)
  reflexivity.
Qed.

Lemma vector0:
  forall (p: PauliVector 0), p = [].
Proof. apply length_0_vector. Qed.


(* Ltac contradict_c_eq H :=
field_simplify_eq in H;
inversion H as [HC];
contradict HC;
lra. *)

Lemma scalar_to_complex_deterministic: forall (a b: phase),
  scalar_to_complex a = scalar_to_complex b ->
  a = b.
Proof.
  intros a b H.
  destruct a, b.
  all: try reflexivity.
  all: try (
    simpl in H;
    inversion H as [HC];
    contradict HC;
    lra
  ).
Qed.

Close Scope group_scope.

(* Move these four to Pauli.v *)
Lemma s_prod_correct_eq: forall (a b c: phase),
  s_prod a b = c <->
  (scalar_to_complex a ) * (scalar_to_complex b) = (scalar_to_complex c).
Proof.
  intros a b c.
  split; intros H.
  - subst. rewrite s_prod_correct; reflexivity.
  - rewrite <- s_prod_correct in H. 
    apply scalar_to_complex_deterministic in H.
    assumption.
Qed.

Lemma s_prod_comm: forall (a b c: phase),
  s_prod a b = c <->
  s_prod b a = c.
Proof.
  intros a b c.
  split; intros H.
  - destruct a, b, c.
    all: try easy.
  - destruct a, b, c.
    all: try easy.
Qed.

Lemma pvec_head:
  forall (n: nat) (va vb: PauliVector (S n)) s v hab sab,
  (s, v) = pvmul va vb ->
  (sab, hab) = op_prod (Vector.hd va) (Vector.hd vb) ->
  Vector.hd v = hab.
Proof.
  intros.
  assert (va = Vector.hd va :: Vector.tl va) by apply eta.
  rewrite H1 in H.
  assert (vb = Vector.hd vb :: Vector.tl vb) by apply eta.
  rewrite H2 in H.
  simpl in H.
  unfold op_prod in H0.
  inversion H0.
  rewrite <- H4 in H.
  rewrite <- H5 in H.
  remember (pvmul (tl va) (tl vb)) as vrest.
  destruct vrest.
  inversion H; subst.
  easy.
Qed.


Lemma pvec_tail:
  forall (n: nat) (va vb: PauliVector (S n)) s v vtl stl,
  (s, v) = pvmul va vb ->
  (stl, vtl) = pvmul (Vector.tl va) (Vector.tl vb) ->
  Vector.tl v = vtl.
Proof.
  intros.
  assert (va = Vector.hd va :: Vector.tl va) by apply eta.
  rewrite H1 in H.
  assert (vb = Vector.hd vb :: Vector.tl vb) by apply eta.
  rewrite H2 in H.
  simpl in H.
  rewrite <- H0 in H.
  remember (op_prod (hd va) (hd vb)) as vhd.
  destruct vhd.
  inversion H; subst.
  easy.
Qed.

Lemma pvec_to_matrix_one_step:
  forall (n: nat) (pvector: PauliVector (S n)) h t,
  Vector.hd pvector = h ->
  Vector.tl pvector = t ->
  pvec_to_matrix pvector = op_to_matrix h ⊗ pvec_to_matrix t.
Proof.
  intros.
  replace pvector with (h::t).
  2: { symmetry. subst. apply VectorSpec.eta. }
  simpl.
  rewrite Mscale_1_l.
  reflexivity.
Qed.


Lemma pvec_prod_scalar_comb:
  forall (n:nat) (va vb: PauliVector (S n)) sab vab ha hb sh hab stl tlab,
  (sab, vab) = pvmul va vb ->
  Vector.hd va = ha ->
  Vector.hd vb = hb ->
  (sh, hab) = op_prod ha hb ->
  (stl, tlab) = pvmul (Vector.tl va) (Vector.tl vb) ->
  sab = s_prod sh stl.
Proof.
  intros.
  replace va with (ha::(tl va)) in H. 
  2: {
    subst.
    symmetry.
    apply VectorSpec.eta.
  }
  replace vb with (hb::(tl vb)) in H.
  2: {
    subst.
    symmetry.
    apply VectorSpec.eta.
  }
  simpl in H.
  rewrite <- H3 in H.
  inversion H2.
  rewrite <- H5 in H.
  rewrite <- H6 in H.
  inversion H; subst.
  apply s_prod_comm.
  reflexivity.
Qed.

Lemma op_prod_clousre_pauli: 
  forall (oa ob: PauliBase),
  exists (p: PauliElem1),
  (op_to_matrix oa) × (op_to_matrix ob) = pauli_to_matrix p.
Proof.
  intros.
  specialize (op_closure oa ob) as Heop.
  destruct Heop as [c [s Hep]].
  exists (p1g_of s c).
  simpl.
  unfold scalar_to_complex, op_to_matrix in Hep.
  rewrite <- Hep.
  reflexivity.
Qed.


Ltac unalias :=
  unfold op_to_matrix, pauli_to_matrix, scalar_to_complex in *.

End PauliString.
From Coq Require Import ssreflect.

(* We show that the two sets of definiton can be transformed from one to 
the another, thus they are of equivalent power *)
Module Adaptor.

Import PauliString.


Notation PauliElementBase := PNBaseGroup.PauliString.

(* This one does work but the type is inconvinient*)
Definition TtoV_l {n:nat} (l: PauliElementBase n): PauliVector (size l) :=
  of_list l.

(* I can prove n = (size l) in tupleToVector *)
Lemma tuple_size:
  forall (n:nat) (tuple: PauliElementBase n),
  size tuple = n.
Proof.
  by move => *; rewrite size_tuple.
Qed.


Fixpoint tupleToVector {n}: (PauliElementBase n) -> PauliVector n :=
  if n is S n return n.-tuple PauliBase -> PauliVector n 
  then fun xs => (thead xs)::(tupleToVector (behead_tuple xs))
  else fun xs => PVector0.

Fixpoint vectorToTuple {n} (v : PauliVector n) : PauliElementBase n :=
  match v with
  | nil => List.nil
  | cons h _ t => List.cons h (vectorToTuple t)
  end.


Theorem vt_isomorphism n:
    cancel (@vectorToTuple n) (@tupleToVector n) /\
    cancel (@tupleToVector n) (@vectorToTuple n).
Proof.
  split.
  {
    move => v.
    induction n.
      by rewrite (vector0 v).
    rewrite (eta v) /=.
    rewrite beheadCons theadCons.
    by rewrite {1}(IHn (VectorDef.tl v)).
  }
  {
    move => t.
    induction n.
      by rewrite (tuple0 t).
    case: t / tupleP => ht tt.
    by rewrite /= theadCons beheadCons IHn.
  }
Qed.

Theorem tupleToVector_correct n:
  forall tup: PauliElementBase n,
  int_pnb tup = pvec_to_matrix (tupleToVector tup).
Proof.
  move => tup.
  induction n.
    by rewrite (tuple0 tup).
  case: tup / tupleP => h t.
  rewrite /= Mscale_1_l theadCons beheadCons.
  by rewrite IHn.
Qed.


Definition pngToPString {n} (png: PauliElement n): PString n :=
  match png with
  |  (phase, tuple) => (phase, tupleToVector tuple)
  end.

Definition pstringToTupleG {n} (pstr: PString n): PauliElement n :=
  match pstr with 
  | (phase, vector) => (phase, vectorToTuple vector)
  end.


Theorem ps_isomorphism n:
    cancel (@pstringToTupleG n) (@pngToPString n) /\
    cancel (@pngToPString n) (@pstringToTupleG n).
Proof.  
  have H0 := vt_isomorphism.
  destruct (H0 n) as [Hvt Htv].
  split. 
  {
    move => [phase vec] /=.
    f_equal.
    by rewrite Hvt.
  }
  {
    move => [phase tup] /=.
    f_equal.
    by rewrite Htv.
  }
Qed.

Import Pauli.

Theorem pngToPstring_correct n:
  forall tupg: PauliElement n,
  int_pn tupg = pstr_to_matrix (pngToPString tupg).
Proof.
  move => tupg.
  case tupg => pha p.
  rewrite /int_pn /pstr_to_matrix /scalar_to_complex /=.
  by rewrite tupleToVector_correct.
Qed.

(* Certified Translation from Tuple to Vector *)
End Adaptor.


