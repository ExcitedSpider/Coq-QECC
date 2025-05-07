(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.
Require Import Coq.Lists.List.
From mathcomp Require Import ssreflect.

Require Import Classical.


(* If P^2 = I, all eigenvalues λ of P satisfy λ^2 = 1 *)
Lemma involutive_eigenvalue n:
  forall (A: Square (2^n)) (psi: Vector (2^n)) (lambda: C),
    A × A = I (2^n) ->
    A × psi = lambda .* psi ->
    lambda = 1 \/ lambda = -1.
Admitted.

(* Let A be a non-zero matrix. if c1 * A = c2 * A, c1 = c2  *)
Lemma Mscale_cancel:
  forall {n m : nat} (c1 c2 : C) (A: Matrix n m),
  A <> (@Zero n m) ->  c1 .* A = c2 .* A -> c1 = c2.
Admitted.
