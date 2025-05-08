(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.
From mathcomp Require Import ssreflect.

(* TODO: This one seems provable *)
Lemma involutoray_matrix_spec {n}:
  forall (A: Square (2^n)),
  A × A = I (2^n) -> A = Minverse A.
Admitted.

Lemma Msub_self {n m}:
  forall (A: Matrix n m),
  A .+ -1 .* A = Zero.
Admitted.

(* Let A be a non-zero matrix. if c1 * A = c2 * A, c1 = c2  *)
(* 1. Check nonzero_vec_nonzero_elem *)
(* 2. Try to make examples not using this items *)
Lemma Mscale_cancel:
  forall {n m : nat} (c1 c2 : C) (A: Matrix n m),
  A <> (@Zero n m) ->  c1 .* A = c2 .* A -> c1 = c2.
Admitted.

Lemma c_sqrt_1_sepcs:
  forall (c: C),
  c ^ 2 = 1 -> c = 1 \/ c = -1.
Admitted.