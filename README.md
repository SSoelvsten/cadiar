# Cadiar : Certified Adiar

This repository provides a formal verification of the core procedures in the
I/O-efficient BDD package [Adiar](https://github.com/SSoelvsten/adiar). The
properties of the data structure and the algorithms were specified and proven
inside of the [Isabelle](https://isabelle.in.tum.de/) proof assistant. This work
reuses many of the ideas in [[Michaelis2016](#references)].

## Usage

1. Download the [Isabelle](https://isabelle.in.tum.de/) proof assistant and open
   this folder at the root.

2. Download the files for [[Michaelis2016](#references)] and place it in a
   folder named _afp-robdd_ at the root.

## Roadmap

### [Adiar 1.0.1](https://github.com/SSoelvsten/adiar/releases/tag/v1.0.1)

Proving correctness of the core algorithms described in
[[Sølvsten2021](#references)].

#### Primary Goals

- Representation of Binary Decision Diagrams
  - [ ] Specification of ordering
  - [ ] Interpretation of list of nodes as the BDD DAG
- CountPaths
  - [ ] Correctness
  - [ ] Time and I/O complexity
- Apply
  - [ ] Correctness
  - [ ] Time and I/O complexity
  - Other
    - [ ] _Optimisation_: Pruning recursion based on operator shortcutting
- Reduce
  - [ ] Correctness
  - [ ] Time and I/O complexity
  - Other
    - [ ] _Optimisation_: Separating arcs to leaves in the input
    - [ ] _Canonicity_: Inductive ordering of nodes, i.e. Proposition 3.5 in the paper.

#### Secondary Goals

- CountSAT (expanding on CountPaths)
- Restrict
- Equality Checking
  - O(sort(N)) variant
  - O(N/B) variant
- If-Then-Else
- 1-variable Quantification

## References

- [[Michaelis2016](https://isa-afp.org/entries/ROBDD.html)]
  Julius Michaelis, Maximilian Haslbeck, Peter Lammich, and Lars Hupel.
  “_Algorithms for Reduced Ordered Binary Decision Diagrams_”. In:
  _Archive of Formal Proofs_ (2016)

- [[Sølvsten2021](https://arxiv.org/abs/2104.12101)]
  Steffan Christ Sølvsten, Jaco van de Pol, Anna Blume Jakobsen, and Mathias
  Weller Berg Thomasen. “_Efficient Binary Decision Diagram Manipulation in
  External Memory_”. In: _arXiv_ (2021)

