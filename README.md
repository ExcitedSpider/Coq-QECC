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
- theoreis-legacy. It is the initial attempt to formalize stabilizer using a from-scratch style. Only quantumLib is used in the project.
- theories. We later did the formalization again using mathcomp and ssreflect, quantum-lib. 
```
.
├── theoreis
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
├── theoreis_legacy
└── readme.md
```

## Status

- Done: The single-qubit Pauli group.
- Done: The n-qubit Pauli group
- Done: Theorems of stabilizer theories. e.g. commute/anti-commute relations.
- Done: Stabilizer Theories using mathcomp formalism
- WIP: examples of proving larger QECC programs correct
- WIP: fill in the holes of formalism.
 
## Acknowledge

This project is developed upon the foundations laid by the [INQWIRE/SQIR](https://github.com/inQWIRE/SQIR) framework, which has provided both inspiration and technical guidance throughout our work. 
We acknowledge and deeply appreciate the exceptional contributions of the SQIR team to the field of quantum programming and formal verification. 
Their open-source efforts have significantly advanced the accessibility and rigor of quantum software development, and we are grateful to be building upon such a well-crafted and thoughtfully designed foundation.

