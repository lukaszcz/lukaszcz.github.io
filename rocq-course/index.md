---
permalink: /rocq/
title: "Theory and Practice of Rocq"
---

# Theory and Practice of Rocq

This is a slightly updated version of a lecture I gave at TU Dortmund in the years 2020 and 2021. Some of the tutorials and exercises require [CoqHammer](https://coqhammer.github.io). The tutorial files have been tested with Coq 8.19.

## Description

Since the beginning of the 21st century, formal proof methods have become standard in industrial hardware verification, particularly in CPU verification ([Intel](https://ieeexplore.ieee.org/document/1210044), [AMD](https://www.russinoff.com/papers/paris.pdf)). During the past decade, the proof assistant technology has matured enough to also enable formal certification of substantial software systems. Major success stories include the [seL4](https://sel4.systems) operating system microkernel, the [CompCert](https://compcert.org) optimising C compiler, and the [CakeML](https://cakeml.org) implementation of Standard ML. Recently, deductive program verification has attracted increasing attention in the software industry ([Microsoft](https://www.microsoft.com/en-us/research/blog/project-everest-advancing-the-science-of-program-proof/), [Amazon](http://www0.cs.ucl.ac.uk/staff/b.cook/CAV18_invited.pdf), [Facebook](https://scontent-waw2-2.xx.fbcdn.net/v/t39.8562-6/240844582_899088944046406_933510202295483783_n.pdf?_nc_cat=101&ccb=1-7&_nc_sid=e280be&_nc_ohc=U9CQaRP6hkQQ7kNvwFxEjKN&_nc_oc=Adk0rTIkh9aAraN-WTSK4qaRvDIePHRM5meCwbmmKsRANxKwzSTOSZ0cOITL1ttPSpyUJ4lvbc4vySeTTKoJAOz0&_nc_zt=14&_nc_ht=scontent-waw2-2.xx&_nc_gid=efFr4y0qAVLavIi4a9TQzQ&oh=00_AfKsBHCRB1-5PNxccoO60yn-XO6Bb8Uqz3XK8bDUpUdmuQ&oe=682D5EB7), [Galois](https://www.galois.com)). To quote Nikhil Swamy from Microsoft Research:

> Today, what seemed impossible just a few years ago is becoming a reality. We can, in certain domains, produce fully verified software at a nontrivial scale and with runtime performance that meets or exceeds the best unverified software.

This lecture is about writing functional programs in a dependently typed language and proving them correct.

[Rocq](https://rocq-prover.org) (formerly Coq) - the 2013 ACM Software System Award winner - is an interactive proof assistant for the development of formally certified software and mathematical theories. Its underlying theory is the Calculus of Inductive Constructions - a variant of dependent type theory with inductive types. The lecture covers programming and proving in Rocq, dependent type theory, and applications to program verification. The focus is on dependently typed functional programming, verification of functional programs, proof automation, theoretical foundations of inductive and dependent types.

## Prerequisites

Some experience with functional programming and formal logic. You should understand mathematical induction. If you liked the logic and/or the functional programming bachelor courses then this lecture is for you. If you're interested in formal methods and security then this may also be for you. The lecture is reasonably self-contained - previous knowledge of type theory is not necessary.

## Supplementary materials

- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) and [Formal Reasoning About Programs](http://adam.chlipala.net/frap/) by Adam Chlipala.
- [Software Foundations](https://softwarefoundations.cis.upenn.edu) by Benjamin C. Pierce et. al.
- [Interactive Theorem Proving and Program Development](https://link.springer.com/book/10.1007/978-3-662-07964-5) by Yves Bertot and Pierre Casteran.
- [Inductive definitions in the system Coq: rules and properties](https://link.springer.com/chapter/10.1007/BFb0037116) by Christine Paulin-Mohring.
- [History of Interactive Theorem Proving](https://www.cl.cam.ac.uk/~jrh13/papers/joerg.pdf) by John Harrison, Josef Urban and Freek Wiedijk.

## Lectures (theory)

1. [Introduction](slides/slides01.pdf)
2. [The Curry-Howard isomorphism](slides/slides02.pdf)
   - [Intuitionistic first-order logic](vrenchouts/predicate.pdf)
3. [Higher-order logic](slides/slides03.pdf)
4. [Dependent types and the Calculus of Constructions](slides/slides04.pdf)
5. [Inductive types](slides/slides05.pdf)
6. [Equality](slides/slides06.pdf)

## Rocq tutorials

1. [Functional programming in Rocq](tutorial/funprog.v)
   - [Basic commands](vrenchouts/commands.pdf)
   - [Notations](vrenchouts/notations.pdf)
   - [Ackermann's function](slides/ackermann.pdf)
2. [Basic logic and proofs](tutorial/logic.v)
   - [Proof terms and tactics for logical connectives](vrenchouts/connectives.pdf)
   - [Basic tactics](vrenchouts/basic_tactics.pdf)
3. [Higher-order logic](tutorial/ho_logic.v)
4. [Equality](tutorial/equality.v)
   - [Equality tactics](vrenchouts/equality_tactics.pdf)
5. [Induction](tutorial/induction.v)
6. [Inductive specifications](tutorial/indspec.v)
7. [Universes and axioms](tutorial/universes.v)
8. [Sorting](tutorial/sorting.v)
9. [Executable specifications](tutorial/boolspec.v)
10. [Strong automation with CoqHammer](tutorial/sauto.v)
11. [Proof automation with Ltac](tutorial/ltac.v)
12. [Dependent types](tutorial/dep_types.v)
13. [Type classes, mergesort and the Function command](tutorial/mergesort.v)
14. [Positivity, large elimination and induction schemes](tutorial/positivity.v)
15. [More dependent types](tutorial/more_dep_types.v)
16. [Dependent pattern matching, the Program command and well-founded recursion](tutorial/matching.v)
17. [Dependently typed expressions](tutorial/dep_expressions.v)
18. [Dependent merge](tutorial/merge.v)
19. [Equality reasoning with dependent types](tutorial/equality.v)
20. [Equations package](tutorial/equations.v)
21. [Program extraction](tutorial/extract.v)
22. [Hoare logic](tutorial/hoare.v)

## Exercises

1. [Functional programming I](exercises/sheets/sheet01.pdf)
2. [Functional programming II](exercises/sheets/sheet02.pdf)
3. [The Curry-Howard isomorphism](exercises/sheets/sheet03.pdf)
4. [Logic; Induction](exercises/sheets/sheet04.pdf)
5. [Induction; Higher-order logic](exercises/sheets/sheet05.pdf)
6. [More induction](exercises/sheets/sheet06.pdf)
7. [Inductive definitions](exercises/sheets/sheet07.pdf)
8. [Induction; Universes](exercises/sheets/sheet08.pdf)
9. [Sorting; Fibonacci](exercises/sheets/sheet09.pdf)
10. [Ltac; Arithmetic expressions; Dependent types](exercises/sheets/sheet10.pdf)
11. [Type classes; Recursors](exercises/sheets/sheet11.pdf)
12. [Search trees I; Dependent pattern matching; Termination](exercises/sheets/sheet12.pdf)
13. [Search trees II](exercises/sheets/sheet13.pdf)
