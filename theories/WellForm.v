Require Import PauliGroup.
From mathcomp Require Import tuple ssreflect.

Require Import SQIR.UnitaryOps.

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