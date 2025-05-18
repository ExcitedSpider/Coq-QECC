 (*
The formalism of Pauli Groups and their quotient groups
In quantum computing, quotied pauli groups are pauligroups without phase
Key Definitions:
- PauliBase: The 1-qubit Pauli quotient group
- phase: The phase {-1, i, -1, -i} and they forms a group
- PauliElem1: The 1-qubit Pauli group
- PauliString: The n-qubit Pauli quotient group
- PauliElement: The n-qubit Pauli group

You can use all canonical definitions in mathcomp: oneg, mulg, invg, idg

This file also contains interpretation:
f: PauliGroup n ->  Matrix 2^n
To bridge group with quantumlib 
*)
From mathcomp Require Import all_ssreflect fingroup.
From HB Require Import structures.
Set Bullet Behavior "Strict Subproofs".


(* 
Shout out to
https://github.com/coq-community/bits
for their tuple lemmas in this section
*)
Section TupleExtras.

Lemma beheadCons {n A} a (aa: n.-tuple A) : behead_tuple [tuple of a::aa] = aa.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma theadCons : forall {n A} (a:A) (aa: n.-tuple A), thead [tuple of a::aa] = a.
Proof. done. Qed.

Lemma zipCons {n A B} a (aa: n.-tuple A) b (bb: n.-tuple B) :
  zip_tuple [tuple of a::aa] [tuple of b::bb] = [tuple of (a,b) :: zip_tuple aa bb].
Proof.
    apply: eq_from_tnth => i.
    rewrite (tnth_nth (a, b)) /=.
    by rewrite (tnth_nth (a, b)) /=.
Qed.

Lemma mapCons {n A B} (f: A -> B) b (p: n.-tuple A) :
  map_tuple f [tuple of b :: p] = [tuple of f b :: map_tuple f p].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (f b)). Qed.

Lemma catCons {n1 n2 A} (a:A) (aa:n1.-tuple A) (bb:n2.-tuple A) :
  cat_tuple [tuple of a::aa] bb = [tuple of a::cat_tuple aa bb].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma catNil {n A} (aa:n.-tuple A) :
  cat_tuple [tuple] aa = aa.
Proof. exact: val_inj. Qed.
  
End TupleExtras. 

Module P1BaseGroup.

Inductive PauliBase : Type :=
| I : PauliBase
| X : PauliBase
| Y : PauliBase
| Z : PauliBase.

Definition mul_p1b(a b: PauliBase): PauliBase :=
  match a, b with
  | X, X => I | X, Y => Z | X, Z => Y 
  | Y, X => Z | Y, Y => I | Y, Z => X 
  | Z, X => Y | Z, Y => X | Z, Z => I 
  | I, p => p | p, I => p 
end.

(* multiplication on PauliBase
Definition mul_p1b(a b: PauliBase): PauliBase :=
  match a, b with
  | I, p => p
  | p, I => p  
  
  | X, X => I
  | Y, Y => I 
  | Z, Z => I

  | X, Y => Z
  | Y, X => Z

  | Y, Z => X
  | Z, Y => X

  | Z, X => Y
  | X, Z => Y 
end. *)

(* All pauli op squares to I *)
Definition inv_p1b (op: PauliBase): PauliBase := op.


(* ID of Pauli_1 group *)
Definition id_p1b := I.

(* Already Proved Properties *)
Definition decode_EE (n: 'I_4) : PauliBase := nth I [:: I;X;Y;Z] (nat_of_ord n).
Definition encode_EE (e: PauliBase) : 'I_4 := 
  match e with
  | I => Ordinal (n:=4) (m:=0) is_true_true
  | X => Ordinal (n:=4) (m:=1) is_true_true
  | Y => Ordinal (n:=4) (m:=2) is_true_true
  | Z => Ordinal (n:=4) (m:=3) is_true_true
  end.

Lemma code_decodeEE : cancel encode_EE decode_EE.
Proof.
  by case.
Qed.

HB.instance Definition _ := Equality.copy PauliBase (can_type code_decodeEE).
HB.instance Definition _ := Finite.copy PauliBase (can_type code_decodeEE).

Lemma mul_p1b_assoc: associative mul_p1b.
Proof. 
  rewrite /associative.
  move => x y z.
  case: x; case: y; case: z; by [].
Qed. 


Lemma mul_p1b_id: left_id id_p1b mul_p1b.
Proof. 
  rewrite /left_id.
  move => x.
  by case: x.
Qed. 

Lemma mul_p1b_left_inv: left_inverse id_p1b inv_p1b mul_p1b.
Proof.
  rewrite /left_inverse.
  move => x.
  by case: x.
Qed.

HB.instance Definition P1BaseGroup := isMulGroup.Build PauliBase
  mul_p1b_assoc mul_p1b_id mul_p1b_left_inv.

End P1BaseGroup.

Module PNBaseGroup.
Import P1BaseGroup.

(* Pauli Group with fixed length n *)
Definition PauliString n := {tuple n of PauliBase}.

Open Scope group_scope.
(* Multiolication on Pauli Group with fixed length n *)
Definition mul_pnb {n: nat} (a b: PauliString n): PauliString n := 
  (map_tuple (fun x => (x.1 * x.2))) (zip_tuple a b).

Definition id_pn n: PauliString n := [tuple of nseq n 1].
(* Definition id_pn n := nseq_tuple n I. *)

Definition inv_pn {n: nat} (pt: PauliString n): PauliString n := map_tuple invg pt.

Example mul_pnb_exp0:
  mul_pnb [tuple X; X] [tuple X; X] == [tuple I; I].
Proof. by []. Qed.

Example mul_pnb_exp1:
  mul_pnb [tuple X; X] [tuple X; X] = [tuple I; I].
Proof. by apply/eqP. Qed.
(* In SSR, you need to change view to computable equality to prompt it compute  *)

Example inv_pn_exp0: 
  inv_pn [tuple X; Y; Z] = [tuple X; Y; Z].
Proof. by apply/eqP. Qed.

Lemma trivial_tuples (p q: PauliString 0) : p = q.
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.

Lemma mul_pnb_cons n:
  forall (hx hy: PauliBase) (tx ty: PauliString n),
    mul_pnb [tuple of hx :: tx] [tuple of hy :: ty] = 
    [tuple of mul_p1b hx hy :: mul_pnb tx ty]
    .
Proof.
  rewrite /mul_pnb => hx hy tx ty.
  by rewrite zipCons mapCons.
Qed.

Lemma mul_pnb_assoc n: associative (@mul_pnb n). 
Proof.
  unfold associative.
  induction n.
  {
    intros.
    apply trivial_tuples.
  }
  {
    intros.
    (* applies view of tupleP *)
    (* Change t: tuple n+1 to t: h::tx *)
    case : x / tupleP => hx tx.
    case : y / tupleP => hy ty.
    case : z / tupleP => hz tz.
    rewrite !mul_pnb_cons. move: (IHn tx ty tz) => ->.
    change mul_p1b with (@mulg PauliBase).
    by gsimpl.
  }
Qed.


Lemma pn_idP {n: nat}: 
  id_pn n.+1 = [tuple of id_p1b :: (id_pn n)].
Proof.
  rewrite /id_pn /id_p1b /=.
  apply: eq_from_tnth => i;
  by rewrite !(tnth_nth I).
Qed.

Lemma mul_pnb_id n: left_id (@id_pn n) (@mul_pnb n).
Proof. 
  unfold left_id.
  induction n.
  1: by intros; apply trivial_tuples. 
  intros.
  case : x / tupleP => hx tx.
  rewrite pn_idP.
  move: IHn.
  rewrite /mul_pnb /id_pn zipCons mapCons=> IHx.
  have IHtx := (IHx tx).
  by rewrite IHtx.
Qed.



Lemma mul_pnb_left_inv n: left_inverse (@id_pn n) (@inv_pn n) (@mul_pnb n).
Proof.
  unfold left_inverse.
  induction n.
    by intros; apply trivial_tuples.
  move => x.
  case : x / tupleP => hx tx.
  move: IHn.
  rewrite /inv_pn mapCons.
  rewrite !mul_pnb_cons.
  change mul_p1b with (@mulg PauliBase); rewrite mulVg.
  move => ->.
  rewrite /id_pn /oneg //= .
  apply eq_from_tnth => i.
  by rewrite !(tnth_nth id_p1b).
Qed.

Section Structure.

Variable n:nat.

HB.instance Definition _ := Finite.on (@PauliString n).

HB.instance Definition _ := isMulGroup.Build 
  (@PauliString n) (@mul_pnb_assoc n) (@mul_pnb_id n) (@mul_pnb_left_inv n).

Check (@PauliString n): finGroupType.

End Structure.

End PNBaseGroup.

(* P1 Group with phase  *)
Module P1Group.

Import P1BaseGroup.

Section PhaseGroup.

Inductive phase : Type :=
| One : phase   (* 1 *)
| Img : phase   (* i *)
| NOne : phase  (* -1 *)
| NImg : phase. (* -i *)

Definition decode_phase (n: 'I_4) : phase := nth One [:: One;Img;NOne;NImg] (nat_of_ord n).
Definition encode_phase (e: phase) : 'I_4 :=
  match e with
  | One => Ordinal (n:=4) (m:=0) is_true_true
  | Img => Ordinal (n:=4) (m:=1) is_true_true
  | NOne => Ordinal (n:=4) (m:=2) is_true_true
  | NImg => Ordinal (n:=4) (m:=3) is_true_true
  end.

Lemma code_decode_phase : cancel encode_phase decode_phase.
Proof.
  by case.
Qed.

HB.instance Definition _ := 
  Equality.copy phase (can_type code_decode_phase).
HB.instance Definition _ := Finite.copy phase (can_type code_decode_phase).


Definition mul_phase (a b : phase) : phase :=
  match a, b with
  | One, x => x
  | x, One => x
  | Img, Img => NOne
  | Img, NOne => NImg
  | Img, NImg => One
  | NOne, Img => NImg
  | NOne, NOne => One
  | NOne, NImg => Img
  | NImg, Img => One
  | NImg, NOne => Img
  | NImg, NImg => NOne
  end.

(* - prove phases form a group *)


Definition inv_phase (sc: phase): phase := 
match sc with
| One => One
| Img => NImg
| NOne => NOne
| NImg => Img 
end.

Definition id_phase := One.

Lemma mult_phase_assoc: associative mul_phase.
Proof.
  rewrite /associative => x y z.
  by case x; case y; case z.
Qed.
  
Lemma mult_phase_id: left_id id_phase mul_phase.
Proof.
  rewrite /left_id => x.
  by case x.
Qed.

Lemma mult_phase_left_inv: left_inverse id_phase inv_phase mul_phase.
Proof.
  rewrite /left_inverse => x.
  by case x.
Qed.

HB.instance Definition PhaseGroup := isMulGroup.Build phase
  mult_phase_assoc mult_phase_id mult_phase_left_inv.

End PhaseGroup.

(* for "Generalized Pauli Operator" *)
Definition PauliElem1 := prod phase PauliBase.

Definition p1g_of: phase -> PauliBase -> PauliElem1 := 
  fun p o => pair p o.

Definition rel_phase(a b: PauliBase): phase :=
  match a, b with  
  | I, _ => One
  | _, I => One
  | X, X => One
  | Y, Y => One 
  | Z, Z => One

  | X, Y => Img
  | Z, X => Img
  | Y, Z => Img

  | Z, Y => NImg
  | Y, X => NImg
  | X, Z => NImg
  end.

Open Scope group_scope.
Definition mul_p1 (a b: PauliElem1): PauliElem1 := 
  match (a, b) with
  | ((sa, pa), (sb, pb)) => (
      rel_phase pa pb * sa * sb, 
      pa * pb
    ) 
  end. 


Definition inv_p1 (a: PauliElem1): PauliElem1 := 
  match a with (s, p) => (s^-1, p^-1) end.

Definition id_p1: PauliElem1 := (1, 1).

Lemma mul_p1_assoc:
  associative mul_p1.
Proof.
  rewrite /associative => x y z.
  case x => sx px.
  case y => sy py.
  case z => sz pz.
  rewrite /mul_p1 /=.
  gsimpl.
  apply injective_projections; rewrite /=; auto.
  (* we first handle a few cases that can be solved without fully unfold *)
  case px, py, pz; try by rewrite /= mult_phase_assoc. 
  (* Then we do brute-force *)
  all: try by case sx, sy, sz.
Qed.

Lemma mul_p1_id:
  left_id id_p1 mul_p1.
Proof.
  rewrite /left_id => x.
  case x => s p.
  by rewrite /mul_p1 /=.
Qed.

Lemma mul_p1_left_inv:
  left_inverse id_p1 inv_p1 mul_p1.
Proof.
  rewrite /left_inverse /id_p1 /inv_p1 /mul_p1 => x.
  case x => s p.
  apply injective_projections; rewrite /=; rewrite ?mulVg.
  gsimpl.
  case p; gsimpl; by rewrite mulVg.
  by rewrite /=.
Qed.

HB.instance Definition _ := Finite.on PauliElem1.
HB.instance Definition P1Group := isMulGroup.Build PauliElem1
  mul_p1_assoc mul_p1_id mul_p1_left_inv.

Notation "%( x ; y )" := (p1g_of x y) (at level 210).

Notation "% x" := (p1g_of One x)  (at level 210).

Notation "-X" := (NOne, X).


End P1Group.

Module PNGroup.

Import P1Group.
Import PNBaseGroup.
Import P1BaseGroup.

Definition rel_phase_pn {n: nat} (a b: PauliString n): phase := 
  foldl mul_phase One (
    map (fun item => rel_phase item.1 item.2)  (zip_tuple a b)
  ).  


Definition PauliElement (n: nat) := prod phase (PauliString n).

Definition rel_phase_png {n: nat} (a b: PauliElement n): phase :=
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      rel_phase_pn pa pb * sa * sb
    )
  end.

Definition mul_pn {n: nat} (a b: PauliElement n): PauliElement n :=
  match (a, b) with
  | (pair sa pa, pair sb pb) => (
      rel_phase_png a b,
      pa * pb
    ) 
end.

Definition inv_png {n}( a: PauliElement n): PauliElement n := 
  match a with
  | pair s p => (s^-1, p^-1)
  end.


Lemma mult_phase_inj: 
  forall a b x y,
  a = x ->
  b = y ->
  mul_phase a b = mul_phase x y.
Proof.
  move => *.
  by subst.
Qed.



Lemma mult_phase_comm:
  commutative mul_phase.
Proof.
  rewrite /commutative => x y.
  by case x, y.
Qed.

Lemma rel_phase_pn_cons n:
  forall (hx hy: PauliBase) (tx ty: PauliString n),
  rel_phase_pn [tuple of hx :: tx] [tuple of hy :: ty] = 
  mul_phase (rel_phase hx hy) (rel_phase_pn tx ty).
Proof.
  intros.
  rewrite /rel_phase_pn  /=.
  rewrite mult_phase_comm.
  rewrite -foldl_rcons /=.
  symmetry.
  rewrite (foldl_foldr mult_phase_assoc mult_phase_comm).
  rewrite foldr_rcons mult_phase_comm.
  rewrite mult_phase_id.
  by rewrite (foldl_foldr mult_phase_assoc mult_phase_comm).
Qed.  


Lemma rel_phase_png_cons {n: nat} :
  forall px py hx hy (tx ty: PauliString n),
    rel_phase_png (px, [tuple of (hx :: tx)]) (py, [tuple of (hy :: ty)])
  = mul_phase (rel_phase hx hy) (rel_phase_png (px, tx) (py, ty)).
Proof.
  move => *.
  rewrite /rel_phase_png rel_phase_pn_cons.
  by rewrite !mult_phase_assoc.
Qed.


Notation "A %* B" := (mul_phase A B) (at level 30).

Lemma mult_phase_simplify:
  forall (a b c d: phase),
  a = c -> b = d ->
  a %* b = c %* d.
Proof. by move => a b c d -> ->. Qed.

Lemma rel_phase_png_assoc n:
  forall (a b c: PauliElement n),
  rel_phase_png (rel_phase_png a b, mul_pnb a.2 b.2) c = 
  rel_phase_png a (rel_phase_png b c, mul_pnb b.2 c.2).
Proof.
  move => [sx px] [sy py] [sz pz].
  (* Fist do all possible simplification *)
  rewrite /rel_phase_png /=; gsimpl.
  apply mult_phase_simplify; try easy.
  apply mult_phase_simplify; try easy.
  rewrite /mulg //=.
  rewrite -!mult_phase_assoc (mult_phase_comm sx) ?mult_phase_assoc.
  apply mult_phase_simplify; try easy.
  (* Nothing can be done. let's induction *)
  induction n.
  - by rewrite (tuple0 px) (tuple0 py) (tuple0 pz) /=.
  - case : px / tupleP => hx tx.
    case : py / tupleP => hy ty.
    case : pz / tupleP => hz tz.
    rewrite !mul_pnb_cons !rel_phase_pn_cons.
    rewrite -!mult_phase_assoc.
    rewrite (mult_phase_comm (rel_phase hx hy)).
    rewrite (mult_phase_comm (rel_phase hy hz)).
    rewrite !mult_phase_assoc.
    rewrite -(mult_phase_assoc (rel_phase (mul_p1b hx hy) hz)) IHn.
    rewrite -!mult_phase_assoc.
    rewrite !(mult_phase_comm (rel_phase_pn ty _)).
    rewrite !mult_phase_assoc.
    apply mult_phase_simplify; try easy.
    rewrite -!mult_phase_assoc.
    rewrite !(mult_phase_comm (rel_phase_pn tx (mul_pnb ty tz))).
    rewrite !mult_phase_assoc.
    apply mult_phase_simplify; try easy.
    by case hx; case hy; case hz.
Qed.

(* Do not try to attempt this! *)
(* This is not valid *)
Lemma rel_phase_png_comm n:
  forall (a b: PauliElement n),
  rel_phase_png a b <>
  rel_phase_png b a.
Abort.
  

Lemma mul_pn_assoc n: 
  associative (@mul_pn n).
Proof.
  rewrite /associative /mul_pn => x y z.
  case x => sx px.
  case y => sy py.
  case z => sz pz.
  f_equal.
  2: by gsimpl.
  by rewrite ?rel_phase_png_assoc.
Qed.

Lemma rel_phase_pn_id n:
  forall v,
  rel_phase_pn (id_pn n) v = One.
Proof.
  move => v.
  induction n.
  by rewrite tuple0 (tuple0 v).
  case : v / tupleP => hv tv.
  rewrite pn_idP /rel_phase_pn /=.
  rewrite /id_pn /rel_phase_pn in IHn.
  by rewrite IHn.
Qed.

Definition id_png (n:nat): PauliElement n := 
  (@oneg phase, @oneg (PauliString n)).

Lemma mul_pn_id n:
  left_id (id_png n) (@mul_pn n).
Proof.
  rewrite  /mul_pn /left_id /= => x.
  case x => s v; gsimpl.
  f_equal.
  rewrite /id_png /rel_phase_png //=; gsimpl.
  rewrite /oneg //= rel_phase_pn_id.
  by gsimpl.
Qed.

Lemma inv_pn_pres_phase n:
  forall (v: PauliString n),
  rel_phase_pn (inv_pn v) v = One.
Proof.
  move => v.
  rewrite /rel_phase_pn.
  induction n.
    by rewrite (tuple0) /=.
  case : v / tupleP => hv tv.
  by case hv; rewrite /= IHn.
Qed.
  

Lemma mul_pn_left_inv n:
  left_inverse (id_png n) inv_png mul_pn. 
Proof.
  rewrite /left_inverse /mul_pn /inv_png /id_png => x.
  case x => p v. 
  rewrite mulVg //=.
  f_equal.
  rewrite /rel_phase_png.
  rewrite {1}/invg //= inv_pn_pres_phase.
  change One with (@oneg phase).
  gsimpl. by rewrite mulVg.
Qed.

Section Strcture.

Variable n: nat.

HB.instance Definition _ := Finite.on (@PauliElement n).
HB.instance Definition _ := isMulGroup.Build
  (@PauliElement n) (@mul_pn_assoc n) (@mul_pn_id n) (@mul_pn_left_inv n).



End Strcture.

End PNGroup.

Require Import QuantumLib.Quantum.
(* Make sure it is loaded *)

(* 
Interprete Pauli Groups (1-qubit and n-qubit) by Robert's QuantumLib
*)
Section Interpretation.

Import P1BaseGroup.

(* 
==========================
interpretation of group p1 
==========================
*)
Definition int_p1b (p : PauliBase) : Square 2 :=
match p with
| I => Matrix.I 2 
| X => Quantum.σx
| Y => Quantum.σy
| Z => Quantum.σz
end.


(* Check action.act act_p1. *)

(* Goal (action.act act_p1 ∣0⟩ X) = ∣1⟩. *)
(* Proof. *)
(*   rewrite /= /apply_p1. *)
(*   by lma'. *)
(* Qed. *)


(* 
==========================
interpretation of group p1g 
==========================
*)

Import P1Group.

Definition int_phase (s: phase): C := 
  match s with
  | One => C1
  | NOne => -C1
  | Img => Ci
  | NImg => - Ci
  end.

Definition int_p1(p: PauliElem1): Square 2 :=
  match p with
  | pair s p => (int_phase s) .* (int_p1b p)
  end.


(* 
==========================
interpretation of group pn 
==========================
*)

Import PNBaseGroup.


Fixpoint int_pnb {n: nat} : (n.-tuple PauliBase) -> Square (2^n) :=
  if n is n'.+1 return (n.-tuple PauliBase) ->  Square (2^n)
  then fun xs => (int_p1b (thead xs)) ⊗ (int_pnb (behead xs))
  else fun _ => Matrix.I 1.

Goal int_pnb [tuple X; Y; Z] = σx ⊗ σy ⊗ σz.
Proof.
  rewrite /=.
  Qsimpl.
  rewrite kron_assoc; auto with wf_db.
Qed.

Definition id1_pn: PauliString 1 := [tuple I].
Lemma mul_pnb_thead n:
forall (hy hx: PauliBase) (ty tx: PauliString n), 
  thead (mul_pnb [tuple of hy :: ty] [tuple of hx :: tx]) = (mulg hy hx) .
Proof.
  intros.
  unfold mul_pnb.
  by rewrite zipCons mapCons theadCons.
Qed.


Lemma mul_pnb_behead n:
forall (hy hx: PauliBase) (ty tx: PauliString n), 
  behead_tuple (mul_pnb [tuple of hy :: ty] [tuple of hx :: tx]) = (mulg ty tx) .
Proof.
  intros.
  unfold mul_pnb.
  by rewrite zipCons mapCons beheadCons.
Qed.


Check kron_assoc.

Ltac int_pnb_simpl :=
  Qsimpl;
  repeat rewrite kron_assoc;
  auto with wf_db.

Example int_pnberpret:
int_pnb [X;Z;Y;I] = σx ⊗ σz ⊗ σy ⊗ Matrix.I 2.
Proof.
  rewrite /int_pnb /=.
  by int_pnb_simpl.
Qed.

(* 
==========================
interpretation of group png
==========================
*)

Import PNGroup.

Definition int_pn {n:nat} (p: PauliElement n): Square (2^n) :=
  match p with
  | (phase, tuple) => (int_phase phase) .* (int_pnb tuple)
  end.

Lemma int_pn_one n:
  forall (pt: PauliString n),
  int_pnb pt = int_pn (One, pt).
Proof.
  move => pt.
  by rewrite /int_pn /= Mscale_1_l.
Qed.

Lemma int_phase_comp: forall x y,
int_phase (mul_phase x y) = int_phase x * int_phase y.
Proof.
  move => x y.
  case x; case y;
  simpl; lca.
Qed.

Print rel_phase_pn.

Lemma rel_phase_pn_behead n:
  forall x y (tx ty: PauliString n),
  (rel_phase_pn [tuple of y :: ty] [tuple of x :: tx]) = 
    mul_phase (rel_phase y x) (rel_phase_pn ty tx).
Proof.
  move => x y tx ty.
  by rewrite rel_phase_pn_cons.
Qed.

Lemma int_p1b_Mmult: forall x y,
  int_p1b y ×  int_p1b x = int_phase (rel_phase y x) .* int_p1b (mulg y x).
Proof.
  move => x y.
  case x; case y; simpl; lma'.
Qed.


Lemma int_pnb_Mmult n: forall (x y: PauliString n),
int_phase (rel_phase_pn x y) .* int_pnb (mul_pnb x y) =
(int_pnb x × int_pnb y).
Proof.
  move => x y.
  induction n.
  - rewrite tuple0 (tuple0 y) /=; lma'.
  - case: x / tupleP; case : y / tupleP => x tx y ty.
    rewrite /= !theadCons !beheadCons /= .
    rewrite kron_mixed_product'; try easy.
    rewrite mul_pnb_behead mul_pnb_thead rel_phase_pn_behead.
    rewrite int_phase_comp int_p1b_Mmult -IHn.
    rewrite !Mscale_kron_dist_l !Mscale_kron_dist_r.
    by rewrite Mscale_assoc.
Qed.
    

Lemma int_pn_Mmult n:
  forall (x y: PauliElement n),
  int_pn x × int_pn y = int_pn (mul_pn x y).
Proof.
  move  => [sx x] [sy y].
  rewrite /int_pn /= /rel_phase_png.
  rewrite !Mscale_mult_dist_r !Mscale_mult_dist_l Mscale_assoc.
  rewrite !int_phase_comp.
  rewrite -int_pnb_Mmult !Mscale_assoc. gsimpl.
  rewrite /mulg //=.
  apply Mscale_simplify; auto; lca.
Qed.

End Interpretation.


Module Export all_pauligroup.
  Export P1BaseGroup.
  Export P1Group.
  Export PNBaseGroup.
  Export PNGroup.
End all_pauligroup.