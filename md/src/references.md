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

- [Jiatu Li - _"Formalization of PAL⋅S5 in Proof Assistant"_](https://arxiv.org/abs/2012.09388)

### Isabelle

#### [Lawrence C. Paulson's _"Gödel's Incompleteness Theorems"_](https://www.isa-afp.org/entries/Incompleteness.html)

Formalized Gödel's first and second incompleteness theorems.
Remark the second incompleteness theorem is proved on hereditarily finite sets.

- [Lawrence C. Paulson, _"A Machine-Assisted Proof of Gödel's Incompleteness Theorems for the Theory of Hereditarily Finite Sets"_](https://arxiv.org/abs/2104.14260)

### HOL/Light

#### [jrh13/hol-light/GL](https://github.com/jrh13/hol-light/tree/master/GL)

  Completeness of Gödel-Löb (provability) modal logic $\bf GL$.

  - [Marco Maggesi, Cosimo Perini Brogi - _"Mechanising Gödel–Löb Provability Logic in HOL Light"_](http://dx.doi.org/10.1007/s10817-023-09677-z)


### Coq

#### [ianshil/PhD_thesis](https://github.com/ianshil/PhD_thesis)

Coq formalization of modal logics and their caliculi for [Ian Shillito, _New Foundations for the Proof Theory of Bi-Intuitionistic and Provability Logics Mechanized in Coq_](https://core.ac.uk/download/pdf/553999288.pdf).

#### [hferee/UIML](https://github.com/hferee/UIML)

Uniform interpolants for basic modal logic $\bf K$, Gödel-Löb provability logic $\bf GL$, intuitionistic strong Löb logic $\bf iSL$.

- [demo](https://hferee.github.io/UIML/demo.html)
- [Hugo Férée, Iris van der Giessen, Sam van Gool, Ian Shillito; _"Mechanised uniform interpolation for modal logics K, GL and iSL"_](https://arxiv.org/abs/2402.10494)
