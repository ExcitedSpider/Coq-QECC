# Coq-QECC

Author: Chew-Yi <chew.y.feng@outlook.com>

Coq-QECC is a Coq (Rocq) formalism of the [quantum stabiliser codes](https://qubit.guide/7-stabilisers).
It is used to provide an abstract approach to reasoning about quantum codes in Coq. 

## Use Case

See [theories/Examples.v](theories/Examples.v).

## Build this Project

If you are new to Coq (Rocq), please first follow [this instruction](https://rocq-prover.org/docs/using-opam) to install opam. 

First, install SQIR and other dependencies:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin coq-sqir https://github.com/inQWIRE/SQIR.git
opam install . --deps-only
```

Build Coq-QECC
```bash
make
```

## Structure Description

The main theories

``` shell
.
├── theoreis
│   ├── PauliGroup.v # Pauli group 
│   ├── Action.v     # group actions
│   ├── PauliProps.v # Some verified properties of pauli group
│   ├── ExtraSpecs.v # Some linear algebra lemmas
│   ├── WellForm.v   # theories related to state well-formness 
│   ├── Stabilizer.v # Quantum stabilizer theory
│   ├── Observable.v # Pauli Observables
│   ├── QECC.v       # Abstract Quantum Error Correction Codes 
│   ├── Example.v    # Examples of Verified Codes
│   └── dune
└── readme.md
```

## Acknowledge

This project is developed upon the foundations laid by the [INQWIRE/SQIR](https://github.com/inQWIRE/SQIR) framework, which has provided both inspiration and technical guidance throughout our work. 
We acknowledge and deeply appreciate the exceptional contributions of the SQIR team to the field of quantum programming and formal verification. 
Their open-source efforts have significantly advanced the accessibility and rigor of quantum software development, and we are grateful to be building upon such a well-crafted and thoughtfully designed foundation.

