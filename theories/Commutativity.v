From mathcomp Require Import ssrfun ssreflect fingroup.
Require Import ExtraSpecs.
Require Import PauliGroup.
Require Import Action.
Require Import QuantumLib.Quantum.
 
Lemma phase_comm n:
 forall (sx sy:phase) (pt: PauliString n),
 (* mulg cannot be inferenced here *)
 mul_pn (sx, pt) (sy, pt) = mul_pn (sy, pt) (sx, pt).
Proof.
  move => sx sy pt.
  rewrite /mul_pn //= /rel_phase_n //=; gsimpl; f_equal. 
  rewrite /mulg //=.
  rewrite -mult_phase_assoc.
  rewrite (mult_phase_comm _ sy).
  by rewrite !mult_phase_assoc.
Qed.

Lemma commute_png_implies n:
  forall (px py: phase) (tx ty: PauliString n),
  commute_at mul_pn (px, tx) (py, ty)-> mul_pnb tx ty = mul_pnb ty tx /\
   rel_phase_n (px, tx) (py, ty) = rel_phase_n (py, ty) (px, tx).
Proof.
  rewrite /commute_at /mul_pn /= => px py tx ty H.
  apply pair_inj in H.
  destruct H as [H1 H2].
  change mul_pnb with (@mulg (PauliString n)).
  by rewrite H1 H2.
Qed.

Lemma mul_p1b_comm:
  commutative mul_p1b.
Proof.
  rewrite /commuteg => x y.
  by case x; case y.
Qed.

Lemma phase_mul_p1b_comm:
  forall hx hy,
  rel_phase hx hy = rel_phase hy hx ->
  mul_p1b hx hy = mul_p1b hy hx.
Proof.
  move => x y.
  by case x; case y.
Qed.

Lemma PauliOp_bicommute:
  forall x y,
  rel_phase x y = rel_phase y x \/
  rel_phase x y = neg_phase (rel_phase y x).
  (* int_phase (rel_phase x y) = -C1 * int_phase (rel_phase y x). *)
Proof.
  move => x y.
  case x; case y; rewrite /=.
  all: try(by left); rewrite -neg_phase_correct.
  all: try(right; lca).
Qed.
