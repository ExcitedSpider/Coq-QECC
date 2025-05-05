# Coq-QECC

# Formalism of the Stabilizer Theory 

Author: Chew-Yi <qiuyif@student.unimelb.edu.au>

This "Stabilizer" package is the formalism and verification of the quantum stabilizer theory.

## Introduction to Math Background

https://qubit.guide/7-stabilisers

## Build this Project

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin coq-sqir https://github.com/inQWIRE/SQIR.git
opam install . --deps-only

# compile default mathcomp version
make 

# compile barebone version
make barebone
```

## Structure Description

There are two packages in the project.
- barebone. Barebone is the initial attempt to formalize stabilizer using a from-scratch style. Only quantumLib is used in the project.
- mathcomp. As the name suggests, we later did the formalization again using mathcomp and ssreflect, quantum-lib. 

```
.
├── barebone 
│   ├── ExtraSpecs.v # extra properties
│   ├── Group.v # from-scratch group definition
│   ├── PauliList.v # Coq.List based n-qubit pauli string
│   ├── PauliString.v # Coq.Vector-based n-qubit pauli string
│   ├── Pauli.v # inductively defined 1-qubit pauli operator
│   ├── Stablizer.v # quantum stabilizer theory
│   └── dune
├── mathcomp
│   ├── PauliGroup.v # Pauli group definition based on math-comp
│   ├── Action.v # definitions of group actions
│   ├── Stabilizer.v # quantum stabilizer theory
│   ├── PauliProps.v # extra verified properties of pauli group
│   ├── ExtraSpecs.v # extra definitions of specifications (TODO: replace with mathcomp)
│   ├── WellForm.v # theories related to state well-formness 
│   ├── Example.v # Some examples for demonstrating stabilizers
│   ├── Assumption.v # Assumptions we used 
│   ├── Adapter.v # adaptor to barebone.PauliString
│   └── dune
└── readme.md
```

## Status

- Done: The single-qubit Pauli group.
- Done: The n-qubit Pauli group
- Done: Theorems of stabilizer theories. e.g. commute/anti-commute relations.
- Done: Stabilizer Theories using mathcomp formalism
- WIP: examples of proving larger QECC programs correct
- WIP: fill in the holes of formalism.
Verification 

## Building instructions

### Installing dependencies

The recommended way to install Coq and other dependencies is via
the [Coq Platform](https://github.com/coq/platform/releases/latest).
To install dependencies manually via [opam](https://opam.ocaml.org/doc/Install.html):
```shell
```
