(* Axioms of Linear Algebra *)
From mathcomp Require Import ssreflect.

Require Import QuantumLib.Quantum.

(* If A is an involutary matrix, A equal to its inverse *)
(* If A^2 = I then A^-1 = A *)
Axiom involutary_matrix_spec:
  forall {n:nat} (A: Square (2^n)),
  A × A = I (2^n) -> A = Minverse A.

(* For any nonzero matrix, there exists i j that A[i,j] is not 0 *)
Axiom Mnonzero_spec:
  forall {n m : nat} (A: Matrix n m),
  WF_Matrix A ->
  A <> Zero -> 
  exists i j , (i < n)%nat /\ (j < m)%nat /\ A i j <> 0.
