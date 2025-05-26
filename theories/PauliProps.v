Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Matrix.
From mathcomp Require Import ssrfun fingroup eqtype fintype.
From mathcomp Require Import seq tuple.

Require Import PauliGroup.
Import PauliGroup.P1BaseGroup.
Import PauliGroup.P1Group.


Import PNBaseGroup.
Import PNGroup.

From mathcomp Require Import ssreflect.

Lemma id_int_pnb:
  forall (n: nat), int_pnb (id_pn n) = Matrix.I (2^n).
Proof.
  intros.
  induction n.
    by rewrite /int_pnb.
  rewrite pn_idP.
  rewrite /= beheadCons IHn.
  restore_dims.
  rewrite id_kron.
  lma'.
Qed.

Lemma id_int_pn:
  forall (n: nat), int_pn (id_png n) = Matrix.I (2^n).
Proof.
  move => n.
  rewrite /id_png /int_pn /=.
  by rewrite Mscale_1_l id_int_pnb.
Qed.


Lemma int_pnb_cons:
  forall {n: nat} (pt: PauliString n) (p: PauliBase),
  int_pnb [tuple of p::pt] = (int_p1b p) ⊗ int_pnb pt.
Proof.
  rewrite /=  => n pt p.
  rewrite theadCons.
  apply kron_simplify.
  - by easy.
  - apply f_equal .
    by rewrite beheadCons.
Qed.


Lemma pauli_unitary n:
  forall (op: PauliString n),
  WF_Unitary (int_pn (One, op)).
Proof.
  move => t //=; Qsimpl.
  induction n.
    case t => p tup; rewrite tuple0 //=; apply id_unitary.
  case /tupleP: t => h t.
  rewrite int_pnb_cons.
  apply kron_unitary.
  - case h; simpl.
    apply id_unitary. 
    apply σx_unitary. 
    apply σy_unitary. 
    apply σz_unitary.
  - apply IHn.
Qed. 

From mathcomp Require Import all_ssreflect.

Lemma p1_involutive :
  forall (p: PauliBase), mulg p p = I.
Proof. by move => p; case p. Qed.

Lemma pauli_involutive {n}:
  forall (op: PauliString n),
  (mulg op op) = (id_pn n).
Proof.
  move => op.
  induction n.
  rewrite tuple0 /id_pn /=. 
  by apply /eqP.
  case: op / tupleP => h t.
  rewrite /mulg /= mul_pnb_cons.
  rewrite /mulg /= in IHn.
  rewrite IHn.
  change mul_p1b with (@mulg PauliBase). 
  rewrite pn_idP.
  by rewrite p1_involutive.
Qed.


Lemma fold_rel_phase_involutive n:
  forall (op: PauliString n),
  fold_rel_phase op op = One.
Proof.
  move => op.
  induction n.
    by rewrite tuple0; apply /eqP.
   case: op / tupleP => h t.
   rewrite fold_rel_phase_cons IHn.
   by case h.
Qed.


Lemma rel_phase_n_involutive:
forall {n} (t: PauliString n), rel_phase_n (One, t) (One, t) = One.
Proof.
  move => n t.
  by rewrite /rel_phase_n fold_rel_phase_involutive /=.
Qed.

Section WellFormness. 
Import P1BaseGroup.
Import P1Group.
Import PNBaseGroup.
Import PNGroup.


Lemma int_p1b_wf:
  forall p: PauliBase,
  WF_Matrix (int_p1b p).
Proof.
  case;
  rewrite /=;
  by auto with wf_db.
Qed.

Lemma int_p1_wf:
  forall p: PauliElem1,
  WF_Matrix (int_p1 p).
Proof.
  move => p.
  case p => ph op.
  rewrite /int_p1.
  apply WF_scale.
  apply int_p1b_wf.
Qed.

Theorem int_pnb_wf n:
  forall (op: PauliString n),
  WF_Matrix (int_pnb op).
Proof.
  intros.
  induction n.
  - rewrite tuple0.
    unfold int_pnb.
    simpl.
    auto with wf_db.
  - case: op / tupleP => x t.
    apply WF_kron; try easy.
    by apply int_p1b_wf.
Qed.

Theorem int_pn_wf n:
  forall (op: PauliElement n),
  WF_Matrix (int_pn op).
Proof.
  move => [p t].
  rewrite /int_pn.
  apply: WF_scale. 
  by apply: int_pnb_wf.
Qed.

End WellFormness.

#[export] Hint Resolve int_p1b_wf int_p1_wf int_pnb_wf int_pn_wf : wf_db.