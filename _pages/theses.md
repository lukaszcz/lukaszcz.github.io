---
permalink: /theses/
title: "Thesis topic proposals (Abschlussarbeitenthemenvorschläge)"
toc: true
---

Die Abschlussarbeiten können auf Englisch oder auf Deutsch geschrieben
werden. Diese Seite ist auf Englisch, weil ich Englisch besser
kenne. Unten folgen Themenvorschläge für Abschlussarbeiten die
[ich](https://ls14-www.cs.tu-dortmund.de/cms/de/mitarbeiter/wimis/Czajka.html)
betreuen will.

The following are some proposals for master thesis topics which
[I](https://ls14-www.cs.tu-dortmund.de/cms/de/mitarbeiter/wimis/Czajka.html)
am willing to supervise. *It is not necessary to address all goals
listed for a given topic.* Only one or some may be sufficient for a
master or a bachelor thesis, depending on which ones and in how much
depth they are treated. Contact me to talk about the details:
lukasz.czajka at tu-dortmund.de (can be in German if you like).

It is also possible to propose your own topic, or I can invent a topic
not listed here, in the following broad areas: functional programming,
programming languages (theory and implementation), proof assistants,
logic and type theory, automated theorem proving, deductive program
verification.

Some paper links below require a subscription and are therefore
accessible only through the university network.

Formalization of functional data structures
-------------------------------------------

Choose some of your favourite functional data structures (e.g. from
[1]) and formalize them in Coq [2] or Isabelle/HOL. For a bachelor
thesis, only a good implementation of a nontrivial functional data
structure in Haskell or OCaml may be sufficient.

### References
1. C. Okasaki: [Purely functional data structures](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf)
2. Y. Bertot: [Coq in a hurry](https://cel.archives-ouvertes.fr/file/index/docid/459139/filename/coq-hurry.pdf)

### Prerequisites
* Functional programming
* Coq or Isabelle/HOL (unless only implementation is done)

### Suggested courses
* [ATLSE](https://ls14-www.cs.tu-dortmund.de/cms/de/Lehre/Lehrveranstaltungen/2020SS/ATLSE/index.html)


Machine-learning premise selection
----------------------------------

Hammers [3] are automated reasoning tools for proof assistants [1],
which combine machine-learning with automated theorem proving. A
typical use is to prove relatively simple goals using available
lemmas. The problem is to find appropriate lemmas in a large
collection of all accessible lemmas and combine them to prove the
goal.

The machine-learning component of a hammer, called premise selection,
tries to solve the following problem: given a large library of lemma
statements together with their proofs, and a goal statement G, predict
which lemmas are likely useful for proving G. For machine-learning
purposes, proofs are usually reduced to a set of dependencies. A
dependency of a lemma L is any lemma which is used in a proof of
L. Hence, given a large dataset of lemma statements with their
dependencies, we want to predict an over-approximation of the set of
dependencies of a new statement.

CoqHammer [4,5] is a hammer tool for [Coq](http://coq.inria.fr) [1] --
a proof assistant based on dependent type theory. The goal of a thesis
would be to improve premise selection in CoqHammer by adapting the
work done for other proof assistants.

### Goals
* Design a better set of features, basing on [6].
* Implement more machine-learning methods and compare them [3, Section 2].
* Investigate adapting a deep learning approach [7].

A Bachelor thesis for this topic could concentrate only on the first
goal: better feature design.

### References
1. H. Geuvers: [Proof Assistants: History, Ideas and Future](https://www.ias.ac.in/article/fulltext/sadh/034/01/0003-0025)
2. Y. Bertot: [Coq in a hurry](https://cel.archives-ouvertes.fr/file/index/docid/459139/filename/coq-hurry.pdf)
3. J. Blanchette, C. Kaliszyk, L. Paulson, J. Urban: [Hammering
towards QED](https://people.mpi-inf.mpg.de/~jblanche/h4qed.pdf)
4. [CoqHammer](https://coqhammer.github.io)
5. Ł. Czajka, C. Kaliszyk: [Hammer for Coq: Automation for Dependent Type Theory](https://link.springer.com/article/10.1007/s10817-018-9458-4)
6. C. Kaliszyk, J. Urban, J. Vyskocil: [Efficient Semantic
   Features for Automated Reasoning over Large Theories](https://www.ijcai.org/Abstract/15/435)
7. A. Alemi, F. Chollet, N. Elen, G. Irving, C. Szegedy, J. Urban:
   [DeepMath - Deep Sequence Models for Premise Selection](https://arxiv.org/abs/1606.04442)

### Prerequisites
* Machine learning
* Functional programming
* Coq and type theory (only superficial knowledge of Coq and type
  theory is necessary as a prerequisite, but deeper knowledge will
  help)

### Suggested courses
* [Maschinelles Lernen](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Intelligente_Systeme/INF-MSc-506.pdf)
* [ATLSE](https://ls14-www.cs.tu-dortmund.de/cms/de/Lehre/Lehrveranstaltungen/2020SS/ATLSE/index.html)


Improvements of CoqHammer
-------------------------

CoqHammer [1,2] (see also the previous topic) is an automated
reasoning tool for Coq - currently the most recognisable and popular
such tool for Coq. However, there are many aspects of CoqHammer that
could be improved. See the
[TODO file](https://github.com/lukaszcz/coqhammer/tree/coq8.13/TODO.md)
for a list of current problems. Some of these problems are suitable as
topics for a Master thesis. A good and ambitious student could also
base a Bachelor thesis on a (partial) solution to one of the
problems. If you're interested in contributing to a cutting-edge
research software project used by many people, ask me about the
details.

### References
1. [CoqHammer](https://coqhammer.github.io)
2. Ł. Czajka, C. Kaliszyk: [Hammer for Coq: Automation for Dependent Type Theory](https://link.springer.com/article/10.1007/s10817-018-9458-4)

### Prerequisites
* Coq and LTac
* Functional programming

### Suggested courses
* [ATLSE](https://ls14-www.cs.tu-dortmund.de/cms/de/Lehre/Lehrveranstaltungen/2020SS/ATLSE/index.html)
* [LMSE1](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-325.pdf) and [LMSE2](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-326.pdf)


Proof search in intuitionistic first-order logic
------------------------------------------------

The goal of a thesis would be to generalise slightly some results from
the literature [1,2,3] on the decidability of certain fragments of
intuitionistic first-order logic and implement decision procedures for
these fragments. Also implement an extension of the Intuition prover
[4], which searches for proofs in minimal first-order logic (i.e. the
universal-implicational fragment of intuitionistic logic), to handle
all connectives.

### Goals
* Extend the result from [1] on EXPSPACE-completeness of the negative
  fragment of minimal first-order logic without function symbols to
  handle all connectives and function symbols with the restriction
  that the size of each individual term occurring in a proof must be
  bounded by a constant. Analogously, extend the result from [1] on
  the co-NEXPTIME-completeness of the arity-bounded negative fragment
  of minimal first-order logic without function symbols.
* Adapt the results of [7] to show EXPTIME-completeness of the Horn
  fragment (i.e. derivability of an atom from a set of Horn clauses)
  with restrictions as in the previous point.
* Implement the above decision procedures.
* Extend Intuition [4] to handle all connectives, basing on [5]. The
  paper [5] and the current procedure of Intuition are based on an
  extension of the automata-theoretic algorithm from [6].
* Implement a decision procedure for the positive fragment [2,3]. This
  goal is hard and could constitute a Master thesis by itself if done
  in sufficient depth.

A Bachelor thesis for this topic could concentrate only on the
implementation, possibly only for the universal-implicational
variants of the fragments without function symbols.

### References
1. A. Schubert, P. Urzyczyn,
    K. Zdanowski: [On the
    Mints Hierarchy in First-Order Intuitionistic Logic](https://lmcs.episciences.org/2623)
2. G. Mints: [Solvability of the problem of deducibility in LJ for a class
        of formulas not containing negative occurrences of
        quantifiers](http://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=tm&paperid=2929&option_lang=eng)
3. G. Dowek,
    Y. Jiang: [Eigenvariables,
    bracketing and the decidability of positive minimal intuitionistic
    logic](https://www.sciencedirect.com/science/article/pii/S1571066104807552)
4. [Intuition prover](https://www.mimuw.edu.pl/~alx/intuition/)
5. M. Zielenkiewicz, A. Schubert:
    [Automata Theory Approach to Predicate Intuitionistic Logic](https://arxiv.org/abs/1608.05698)
6. A. Schubert, W. Dekkers, H. Barendregt:
    [Automata Theoretic Account of Proof Search](http://drops.dagstuhl.de/opus/volltexte/2015/5411/)
7. B. Düdder, M. Moritz, J. Rehof, P. Urzyczyn:
    [Bounded Combinatory Logic](http://drops.dagstuhl.de/opus/volltexte/2012/3676/)

### Prerequisites
* Logic and type theory

### Suggested courses
* [LMSE1](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-325.pdf) and [LMSE2](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-326.pdf)
* [Komplexitätstheorie](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Basismodule/Forschungsbereich_Algorithmen_und_Komplexitaet/INF-MSc-242.pdf)


Proof search in Pure Type Systems
---------------------------------

The goal of a thesis would be to compare and/or implement the proof
search procedures for Pure Type Systems (or the Lambda-Cube) from the
papers [1,2].

### References
1. G. Dowek: [A Complete Proof Synthesis Method for the Cube of Type Systems](https://academic.oup.com/logcom/article/3/3/287/980271)
2. S. Lengrand, R. Dyckhoff, J. McKinna: [A Focused Sequent Calculus Framework for Proof Search in Pure Type Systems](https://arxiv.org/abs/1012.3372)

### Prerequisites
* Logic and type theory

### Suggested courses
* [LMSE1](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-325.pdf) and [LMSE2](http://www.cs.tu-dortmund.de/nps/de/Studium/Ordnungen_Handbuecher_Beschluesse/Modulhandbuecher/Master_Inf/Vertiefungsmodule/Forschungsbereich_Software_Sicherheit_und_Verifikation/INF-MSc-326.pdf)
