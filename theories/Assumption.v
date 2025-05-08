(* Assumption we made for the formalization *)
From mathcomp Require Import ssreflect.

Require Import QuantumLib.Quantum.

(* If A is an involutary matrix, A = A^-1 *)
Lemma involutary_matrix_spec {n}:
  forall (A: Square (2^n)),
  A × A = I (2^n) -> A = Minverse A.
Admitted.

(* For any nonzero matrix, there exists i j that A[i,j] is not 0 *)
Lemma Mnonzero_spec:
  forall {n m : nat} (A: Matrix n m),
  WF_Matrix A ->
  A <> Zero -> 
  exists i j , (i < n)%nat /\ (j < m)%nat /\ A i j <> 0.
Admitted.
