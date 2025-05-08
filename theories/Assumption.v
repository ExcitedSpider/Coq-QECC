(* Assumption we made for the formalization *)

Require Import QuantumLib.Quantum.
From mathcomp Require Import ssreflect.

(* If A is an involutary matrix, A = A^-1 *)
Lemma involutary_matrix_spec {n}:
  forall (A: Square (2^n)),
  A × A = I (2^n) -> A = Minverse A.
Admitted.

(* For any complex number c, c = ±1 if c^2 = 1 *)
Lemma c_sqrt_1_spec:
  forall (c: Complex.C),
  c ^ 2 = 1 -> c = 1 \/ c = -1.
Admitted.

(* For any nonzero matrix, there exists i j that A[i,j] is not 0 *)
Lemma Mnonzero_spec:
  forall {n m : nat} (A: Matrix n m),
  WF_Matrix A ->
  A <> Zero -> 
  exists i j , (i < n)%nat /\ (j < m)%nat /\ A i j <> 0.
Admitted.

Lemma Cmult_neq:
  forall (a c1 c2: C),
  a <> 0 -> c1 <> c2 -> c1 * a <> c2 * a.
Admitted. 
