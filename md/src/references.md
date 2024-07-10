# References and Related Works

## References

- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
- 菊池 誠 (編者), 『数学における証明と真理 ─ 様相論理と数学基礎論』
- P. Blackburn, M. de Rijke, Y. Venema, "Modal Logic"
- Open Logic Project, ["The Open Logic Text"](https://builds.openlogicproject.org/)
- R. Hakli, S. Negri, "Does the deduction theorem fail for modal logic?"
- G. Boolos, "The Logic of Provability"
- M. C. Fitting, V. W. Marek, and M. Truszczynski, _"The Pure Logic of Necessitation"_
- T. Kurahashi, _"The provability logic of all provability predicates"_
- W. Carnielli, C. Pizzi, _"Modalities and Multimodalities"_

## Related Works

Here is the list of project particularly formalize mathematical logics.
If you find something missing from this list or add, report via [issues](https://github.com/iehality/lean4-logic/issues).

### Lean 4

#### [m4lvin/lean4-pdl](https://github.com/m4lvin/lean4-pdl)

Propositional dynamic logics.


#### [alexoltean61/hybrid_logic_lean](https://github.com/alexoltean61/hybrid_logic_lean)

Hybrid logic.
Syntax and semantics for hybrid logic are provided, and some facts and soundness have been proven.
However [completeness seems to have been not yet formalized](https://github.com/alexoltean61/hybrid_logic_lean/blob/5ce7b680763fd7fed1404f294478757bb52dea18/Hybrid/Completeness.lean#L62-L67).

- [Andrei-Alexandru Oltean, _"A Formalization of Hybrid Logic in Lean"_](https://raw.githubusercontent.com/alexoltean61/alexoltean61.github.io/main/hybrid.pdf)


#### [leanprover-community/con-nf](https://github.com/leanprover-community/con-nf)

Formalizing the consistency of Quine's set theory "New Foundations": $\mathrm{Con}(\mathbf{NF})$.

- [Website](https://leanprover-community.github.io/con-nf/)

### Lean 3

#### [flypitch](https://flypitch.github.io/)

Independence of the continuum hypothesis.

- [Jesse Michael Han and Floris van Doorn, "A Formal Proof of the Independence of the Continuum Hypothesis"](https://flypitch.github.io/assets/flypitch-cpp.pdf)

#### [bbentzen/ipl](https://github.com/bbentzen/ipl)

Intuitionistic propositional logic.

Hilbert-style deduction system, Kripke semantics and Henkin-style (constructing maximal prime set and canonical model) completeness proof.

- [Huayo Guo, Dongheng Chen, Bruno Bentzen, _"Verified completeness in Henkin-style for intuitionistic propositional logic"_](https://arxiv.org/abs/2310.01916)


####  [bbentzen/mpl](https://github.com/bbentzen/mpl/)

Normal modal logic.

Hilbert-style deduction system, Kripke semantics and Henkin-style (constructing maximal consistent set and canonical model) completeness proof for $\bf S5$.

- [Bruno Bentzen, _"A Henkin-style completeness proof for the modal logic S5"_](https://arxiv.org/abs/1910.01697)


#### [paulaneeley/modal](https://github.com/paulaneeley/modal)

Formalization of modal logic $\bf S5$ and public announcement logic.

- [Paula Neeley, _"A Formalization of Dynamic Epistemic Logic"_](https://paulaneeley.com/wp-content/uploads/2021/05/draft1.pdf)



#### [minchaowu/ModalTab](https://github.com/minchaowu/ModalTab)

Tableaux system for modal logic $\bf K, KT, S4$.

- [Minchao Wu, Rajeev Goré, _"Verified Decision Procedures for Modal Logics"_](https://doi.org/10.4230/LIPIcs.ITP.2019.31)



#### [ljt12138/Formalization-PAL](https://github.com/ljt12138/Formalization-PAL)

$\bf S5$ and public announcement logic (PAL).
Main result are recursion theorem (reducing public announce modality for any PAL formula) and completeness of $\bf S5$.

- [Jiatu Li, _"Formalization of PAL⋅S5 in Proof Assistant"_](https://arxiv.org/abs/2012.09388)

### Isabelle

#### [Lawrence C. Paulson, _"Gödel's Incompleteness Theorems"_](https://www.isa-afp.org/entries/Incompleteness.html)

Formalized Gödel's first and second incompleteness theorems.
Remark the second incompleteness theorem is proved on hereditarily finite sets.

- paper: [Lawrence C. Paulson, _"A Machine-Assisted Proof of Gödel's Incompleteness Theorems for the Theory of Hereditarily Finite Sets"_](https://arxiv.org/abs/2104.14260)

#### [Christoph Benzmüller, Woltzenlogel Paleo, _"Gödel's God in Isabelle/HOL"_](https://www.isa-afp.org/entries/GoedelGod.html)

Gödel's ontological argument of God's existence.

#### [jrh13/hol-light/GL](https://github.com/jrh13/hol-light/tree/master/GL)

Completeness of Gödel-Löb (provability) modal logic $\bf GL$ in HOL/Light.

  - [Marco Maggesi, Cosimo Perini Brogi, _"Mechanising Gödel–Löb Provability Logic in HOL Light"_](http://dx.doi.org/10.1007/s10817-023-09677-z)

#### [u5943321/Modal-Logic](https://github.com/u5943321/Modal-Logic)

Modal Logic, based on textbook _"Modal Logic"_ by P. Blackburn, M. de Rijke, Y. Venema in HOL.

- [Yiming Xu, _"Formalizing Modal Logic in HOL"_](https://tqft.net/web/research/students/YimingXu/thesis.pdf)

### Coq

#### [ianshil/PhD_thesis](https://github.com/ianshil/PhD_thesis)

Coq formalization of several modal logics (related provability logic and etc.) and their caliculi.

- [Ian Shillito, _New Foundations for the Proof Theory of Bi-Intuitionistic and Provability Logics Mechanized in Coq_](https://core.ac.uk/download/pdf/553999288.pdf).

#### [hferee/UIML](https://github.com/hferee/UIML)

Uniform interpolants for basic modal logic $\bf K$, Gödel-Löb provability logic $\bf GL$, intuitionistic strong Löb logic $\bf iSL$.

- [demo](https://hferee.github.io/UIML/demo.html)
- [Hugo Férée, Iris van der Giessen, Sam van Gool, Ian Shillito, _"Mechanised uniform interpolation for modal logics K, GL and iSL"_](https://arxiv.org/abs/2402.10494)

#### [ana-borges/QRC1-Coq](https://gitlab.com/ana-borges/QRC1-Coq/)

Quantified modal logic called _Quantified Reflection Calculus with one modality_ $\sf QRC_1$.

#### [Christian Doczkal, Gert Smolka, _"Completeness and decidability of converse PDL in the constructive type theory of Coq"_](http://doi.org/10.1145/3167088)

Propositional Dynamic Logic.

#### [Christian Doczkal, Gert Smolka, _"Constructive Formalization of Hybrid Logic with Eventualities"_](http://doi.org/10.1007/978-3-642-25379-9_3)

Hybrid Logic.

#### [Russell O'Connor](https://r6.ca/)'s continuous works on Incompleteness Theorem

  - [Russell O’Connor, _"Essential Incompleteness of Arithmetic Verified by Coq"_](https://arxiv.org/pdf/cs/0505034)

#### [fondefjobn/S5-Formalization-in-Coq](https://github.com/fondefjobn/S5-Formalization-in-Coq/)

Modal logic $\bf S5$, its Kripke completeness.

- [Lubor Budaj, _"Formalization of modal logic $\bf S5$ in the Coq proof assistant"_](https://fse.studenttheses.ub.rug.nl/28482/1/BSc_Thesis_final.pdf)

#### [Floris van Doorn, _"Propositional Calculus in Coq"_](https://arxiv.org/pdf/1503.08744)

Hilbert deduction system, natural deduction system, and sequent calculus for classical propositional logic.
Formalized completeness of natural deduction system, the provability equivalence of three calculi, cut-elimination for sequent calculus.

#### [Christoph Benzmüller, Bruno Woltzenlogel Paleo, "Interacting with Modal Logics in the Coq Proof Assistant"](https://www.researchgate.net/publication/273201458_Interacting_with_Modal_Logics_in_the_Coq_Proof_Assistant)

Modal logic and Gödel's ontological argument of existence of God.

#### [mphilipse/coq-multi-agent-systems](https://gitlab.science.ru.nl/mphilipse/coq-multi-agent-systems)

Multi-agent epistemic modal logic $\mathbf{S5}^n$.

- [Michiel Philipse, _"Distributed Knowledge Proofs in the Coq Proof Assistant"_](https://www.cs.ru.nl/bachelors-theses/2021/Michiel_Philipse___1016359___Distributed_Knowledge_Proofs_in_the_Coq_Proof_Assistant.pdf)

#### [Iris Project](https://iris-project.org/)

Framework for concurrent saparation logic. Verified in Coq.
