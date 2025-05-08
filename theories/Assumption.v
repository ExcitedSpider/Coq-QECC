(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.
From mathcomp Require Import ssreflect.

(* If A is an involutary matrix, A = A^-1 *)
Lemma involutary_matrix_spec {n}:
  forall (A: Square (2^n)),
  A × A = I (2^n) -> A = Minverse A.
Admitted.

Lemma c_sqrt_1_spec:
  forall (c: Complex.C),
  c ^ 2 = 1 -> c = 1 \/ c = -1.
Admitted.

(* Let A be a non-zero matrix, c1 = c2 if c1 * A = c2 * A,   *)
Lemma Mscale_cancel:
  forall {n m : nat} (c1 c2 : C) (A: Matrix n m),
  A <> Zero ->  c1 .* A = c2 .* A -> c1 = c2.
Admitted.
