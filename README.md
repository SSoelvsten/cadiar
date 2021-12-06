# Cadiar : Certified Adiar

[![Build](https://github.com/SSoelvsten/cadiar/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/SSoelvsten/cadiar/actions/workflows/ci.yml)

This repository provides a formal verification of the core procedures in the
I/O-efficient BDD package [Adiar](https://github.com/SSoelvsten/adiar) as
described in [[Sølvsten2021](#references)]. The properties of the data structure
and the algorithms were specified and proven inside of the
[Isabelle](https://isabelle.in.tum.de/) proof assistant. This work reuses some
parts of the formalisation of recursive BDDs in [[Michaelis2016](#references)].

## Usage

1. Download the [Isabelle](https://isabelle.in.tum.de/) proof assistant and open
   this folder at the root.

2. We are also dependent on [[Michaelis2016](#references)].

   For this, download the entire [Archive of Formal
   Proofs](https://www.isa-afp.org/download.html) and link Isabelle to it as
   described [here](https://www.isa-afp.org/using.html).

Assuming Isabelle has been added to your path, then you can run Isabelle on the
entire project (and its dependencies) with the following command.
```bash
isabelle build -D cadiar
```

## References

- [[Michaelis2016](https://isa-afp.org/entries/ROBDD.html)] Julius Michaelis,
  Maximilian Haslbeck, Peter Lammich, and Lars Hupel. “_Algorithms for Reduced
  Ordered Binary Decision Diagrams_”. In: _Archive of Formal Proofs_ (2016)

- [[Sølvsten2021](https://arxiv.org/abs/2104.12101)]
  Steffan Christ Sølvsten, Jaco van de Pol, Anna Blume Jakobsen, and Mathias
  Weller Berg Thomasen. “_Efficient Binary Decision Diagram Manipulation in
  External Memory_”. In: _arXiv_ (2021)

