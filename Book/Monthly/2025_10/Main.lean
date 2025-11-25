import Book.Init

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open LO

set_option verso.docstring.allowMissing true

open LO

#doc (Manual) "Monthly Report 2025/10" =>
%%%
tag  := "monthly-report-2025-10"
%%%

This page is the monthly report summarizing commits [between 2025/10/01 and 2025/11/01](https://github.com/FormalizedFormalLogic/Foundation/commits/master/?since=2025-10-01&until=2025-11-01).
There are 3 major topics in this month.

# Set Theory and Consistency of `ZFC`

*Author*: [Palalansoukî](https://github.com/iehality)

-We formalized that [ZFSet](https://leanprover-community.github.io/mathlib4_docs//Mathlib/SetTheory/ZFC/Basic.html#ZFSet)
is a (standard) model of $`\mathsf{ZFC}`.-

_Update (2025/11)_: We use {lean}`FirstOrder.SetTheory.Universe` instead of `ZFSet`.

{docstring FirstOrder.SetTheory.Universe.models_zfc}

As an obvious consequence, it can be proven that $`\mathsf{ZFC}` is consistent.

{docstring FirstOrder.SetTheory.zfc_consistent}

This result should not be seen as supporting the "consistency of mathematics" in the sense of Hilbert's Program.
Rather, it is a natural consequence of Lean 4 possessing multiple type universes,
and it is well-known that Lean is much stronger than $`\mathsf{ZFC + Con(ZFC)}`.
For detail, see {citet Carneiro19}[] and {citet Werner97}[].

# Filteration of Neighborhood Semantics on Modal logic

*Author*: [@SnO2WMaN](https://github.com/SnO2WMaN)

Filtration in neighborhood semantics for modal logic has been studied
mainly for extensions of logic `E` by the axioms `M`, `C`, and `N`,
as well as for non-iterative axioms (i.e., those of modal depth at most 1)
by Lewis's Theorem ({citet Lew74}[]).
However, beyond these cases, very few results are known.

Recently, {citet Kop23}[] showed that logics containing
axiom `4` also enjoy the finite frame property (FFP) via filtration.
Since axiom `4` is not non-iterative,
Lewis’s theorem cannot be applied, and a nontrivial construction of the filtration is required.
However, Kopnev’s work exists only as an arXiv preprint and
does not have been reviewed and officially published.
During our verification, we found one missing case in the proof,
but the main argument remains correct once this gap is addressed.

In this project, we formalized Kopnev’s result.
In particular, formalized the FFP of logics `E4`, `ET4`, `EMC4` and `EMT4` via filtration.

{docstring Modal.E4.Neighborhood.finite_complete}

{docstring Modal.ET4.Neighborhood.finite_complete}

{docstring Modal.EMC4.Neighborhood.finite_complete}

{docstring Modal.EMT4.Neighborhood.finite_complete}

And as easy corollaries about and `N`, also formalized in FFP of `EN4`, `EMCN4`, `EMNT4`.

{docstring Modal.EN4.Neighborhood.finite_complete}

{docstring Modal.EMNT4.Neighborhood.finite_complete}

{docstring Modal.EMCN4.Neighborhood.finite_complete}

Remarks that `EMCN4` is equivalent to `K4`.

*Author note*: We noticed that forgot to formalize the FFP of `EMCNT4`, that is equivalent to `S4`, it might be proved easily.

More information might be found in {ref "modal-logic-neighborhood-semantics"}[chapter of neightborhood semantics on modal logic].
_(work in progress)_

# Interpretability Logic and Veltman Semantics

*Author*: [@SnO2WMaN](https://github.com/SnO2WMaN)

*Author note*: This report described below is under active development,
and some parts may no longer match the implementation at the time of reading.
For precise details, please refer to the latest code or the section {ref "interpretability-logic"}[Interpretability Logic] _(in progress)_.

As a further extension of provability logic, observed *interpretations* between theories are treated as modal operators.
This study is called *interpretability logic*.
Briefly, in interpretability logic, in addition to the usual unary modality $`\Box`, a binary modality $`\rhd` is introduced.

During this month’s progress in FFL, we formalized several syntactic facts of interpretability logic and
introduced Veltman semantics, which is extension of the Kripke semantics by de Jongh and Veltman, and established its soundness.
In this report, we do not discuss the arithmetical completeness of interpretability.
The long-term goal of FFL is to eventually formalize.
Refer to overview of interpretability logic, see {citet Vis97}[], {citet JD98}[], {citet Joo04}[].

Formulas of interpretability logic are defined by extending the language of modal logic with the binary connective `rhd`,
which we will denote by `▷`.

{docstring InterpretabilityLogic.Formula}

Basic axioms and rules of interpretability logic are as follows:

- $`\mathsf{J1}`: $`\Box(\varphi \rightarrow \psi) \rightarrow (\varphi \rhd \psi)`
- $`\mathsf{J2}`: $`(\varphi \rhd \psi) \wedge (\psi \rhd \chi) \rightarrow (\varphi \rhd \chi)`
- $`\mathsf{J2^+}`: $`\varphi \rhd (\psi \lor \chi) \to \psi \rhd \chi \varphi \rhd \chi`
- $`\mathsf{J3}`: $`\varphi \rhd \chi \to \psi \rhd \chi \to (\varphi \lor \psi) \rhd \chi`
- $`\mathsf{J4}`: $`\varphi \rhd \psi \to \Diamond \varphi \to \Diamond \psi`
- $`\mathsf{J4^+}`: $`\Box(\varphi \to \psi) \to (\chi \rhd \varphi \to \chi \rhd \psi)`
- $`\mathsf{J5}`: $`\Diamond \varphi \rhd \varphi`
- $`\mathsf{J6}`: $`\Box \varphi \leftrightarrow \lnot \varphi \rhd \bot`
- $`\mathrm{(R1)}`: From $`\varphi \rightarrow \psi` infer $`\varphi \rhd \psi`
- $`\mathrm{(R2)}`: From $`\varphi \rightarrow \psi` infer $`\psi \rhd \chi \rightarrow \varphi \rhd \chi`

We defines the logics by usual Hilbert system extending modal logic $`\mathbf{GL}`:

- $`\mathbf{IL^-}` is obtained by adding axioms $`\mathsf{J3}` and $`\mathsf{J6}` and rules $`\mathrm{(R1)}` and $`\mathrm{(R2)}`.
- $`\mathbf{IL^-}(\mathsf{X})` is obtained by adding axioms $`\mathsf{X}` to $`\mathbf{IL^-}`, such as $`\mathbf{IL^-}(\mathsf{J2}, \mathsf{J5})`.
- $`\mathbf{CL}` is obtained by adding axioms $`\mathsf{J1}`, $`\mathsf{J2}`, $`\mathsf{J3}`, and $`\mathsf{J4}`.
- $`\mathbf{IL}` is obtained by adding axioms $`\mathsf{J5}` to $`\mathbf{CL}`.

We can prove by syntactically that $`\mathbf{CL}` is equivalent to $`\mathbf{IL^-}(\mathsf{J1}, \mathsf{J2})`, and $`\mathbf{IL}` is equivalent to $`\mathbf{IL^-}(\mathsf{J1}, \mathsf{J2}, \mathsf{J5})`.

{docstring InterpretabilityLogic.equiv_CL_ILMinus_J1_J2}

{docstring InterpretabilityLogic.equiv_IL_ILMinus_J1_J2_J5}

As the semantics for interpretability logic,
the extensions of Kripke semantics (i.e. relational semantics) has been proposed by de Jongh and Veltman.
nowaday this semantics called *Veltman semantics*.

Let $`K := \langle W, R \rangle` be Kripke frame which validate modal logic $`\mathbf{GL}`,
a Veltman frame $`V` is obtained by adding a family of relations $`\{S_w\}_{w \in W}`, indexed by each world to $`K`.
$`S_w` must satisfy only the following property: $`x S_w y \implies w R y`.
As we write $`\prec` and `≺` (in lean) for $`R` in Kripke semantics, we sometimes write $`\prec_w` and `≺[w]` (in lean) for $`S_w`.

{docstring InterpretabilityLogic.Veltman.Frame}

*Remark*: As a terminological remark,
a frame with $`\{S_w\}_{w \in W}` but without further structural conditions is usually not called a Veltman frame.
In the literature, such vanilla structures are referred to as
*Veltman prestructures* ({citet Vis88}[]) or
*$`\mathbf{IL^-}`-frames* ({citet KO21}[]).
However, to avoid unnecessary naming complexity, in our formalization we simply refer to them as Veltman frames.

The notion of a valuation and a model is defined in the same way as in modal logic,
except that the underlying frame is now a Veltman frame.

The satisfaction relation except $`\rhd` is defined same as modal logic.
For $`\rhd` is defined as follows: Let $`M` be a Veltman model and $`w` be a world in $`M`.

```math
M, w \models \varphi \rhd \psi \iff ∀ x, w \prec x ~\&~ M, x \models \varphi, \exists y, x \prec_w y ~\&~ M, y \models \psi
```

With this semantics in place, validity on models and frames is defined analogously to Kripke semantics.

For any Veltman frames, axioms $`\mathsf{J3}`, $`\mathsf{J6}` are valid and rule $`\mathrm{(R1)}` and $`\mathrm{(R2)}` are conserve the validity.

{docstring InterpretabilityLogic.Veltman.validate_axiomJ3}

{docstring InterpretabilityLogic.Veltman.validate_axiomJ6}

{docstring InterpretabilityLogic.Veltman.validate_R1}

{docstring InterpretabilityLogic.Veltman.validate_R2}

Hence, the logic $`\mathbf{IL^-}` is sound with respect to the class of all Veltman frames.

{docstring InterpretabilityLogic.ILMinus.Veltman.sound}

Furthermore, additional frame conditions are required to validate more axioms $`\mathsf{J1}`, $`\mathsf{J2}` ($`\mathsf{J2^+}`), $`\mathsf{J4}` ($`\mathsf{J4^+}`) and $`\mathsf{J5}`.

{docstring InterpretabilityLogic.Veltman.Frame.HasAxiomJ1}

{docstring InterpretabilityLogic.Veltman.validate_axiomJ1_of_J1}

{docstring InterpretabilityLogic.Veltman.Frame.HasAxiomJ2}

{docstring InterpretabilityLogic.Veltman.validate_axiomJ2Plus_of_HasAxiomJ2}

{docstring InterpretabilityLogic.Veltman.Frame.HasAxiomJ4}

{docstring InterpretabilityLogic.Veltman.validate_axiomJ4Plus_of_HasAxiomJ4}

{docstring InterpretabilityLogic.Veltman.Frame.HasAxiomJ5}

{docstring InterpretabilityLogic.Veltman.validate_axiomJ5_of_J5}

Hence, in particular, the logics $`\mathbf{CL}` and $`\mathbf{IL}` are sound with respect to appropriate classes of Veltman frames.

{docstring InterpretabilityLogic.CL.Veltman.sound}

{docstring InterpretabilityLogic.IL.Veltman.sound}

Other axioms of frame correspondences are currently under working and will be reported in the next month update.

We list several goals for future development:
- Currently we did not formalize completeness results.
  Completeness for $`\mathbf{IL}` and some of its extensions was shown by {citet DV90}[] and
  completeness for sublogics of $`\mathbf{IL}` has been established by {citet KO21}[].
  Technically, the latter appears more approachable, and we intend to proceed from there.
- Under arithmetical interpretations, the unary modality $`\Box` has little flexibility,
  i.e. being interpreted as a provability predicate.
  In contrast, the binary modality $`\rhd` admits various interpretations, e.g. conservatibility, interpretability.
  And it would be desirable to formalize arithmetical soundness and completeness results that reflect these interpretations.
- Although Veltman semantics is basic,
  it is known that a technically simpler semantics is useful when considering embedding to arithmetic.
  This simplified semantics is called *simplified Veltman semantics* or *Visser semantics*. See {citet Vis88}[].
  By contrast, enriching the relation $`S_w` is more useful to distinguish more fine frame correspondences to axioms.
  This generalized semantics is called *generalized Veltman semantics* or *Verbrugge semantics*.
  See {citet JRMV24}[] the overview of Verbrugge semantics.
  These two semantics exhibit a trade-off between technical flexibility and frame correspondences.
  We plan to formalize both, for arithmetical completeness and separation of logics.
  To note that for Verbrugge semantics,
  prior formalizations exist in Agda (and Coq) in {citet Rov20}[].
  This formalization is particularly concerning axiom characterization and soundness, which we also intend to extend.

# Commits

- `3a9f118c`: add(FirstOrder): ZFC is consistent ([#606](https://github.com/FormalizedFormalLogic/Foundation/pull/606))
- `fee7c6e4`: add(FirstOrder): forcing part.1 ([#604](https://github.com/FormalizedFormalLogic/Foundation/pull/604))
- `fc53bbd3`: add(InterpretabilityLogic): Veltman semantics and soundness ([#602](https://github.com/FormalizedFormalLogic/Foundation/pull/602))
- `263961ed`: refactor(FirstOrder): structure ([#603](https://github.com/FormalizedFormalLogic/Foundation/pull/603))
- `b41e28ef`: refactor(FirstOrder): refactor arithmetic ([#573](https://github.com/FormalizedFormalLogic/Foundation/pull/573))
- `d97591fe`: add(FirstOrder): downward Löwenheim-Skolem theorem ([#599](https://github.com/FormalizedFormalLogic/Foundation/pull/599))
- `a5548d9a`: rename(FirstOrder): `Interpretation` ↦ `DirectInterpretation`  ([#598](https://github.com/FormalizedFormalLogic/Foundation/pull/598))
- `7285d2a1`: add(FirstOrder/SetTheory): cardinals in set theory, part 1 ([#579](https://github.com/FormalizedFormalLogic/Foundation/pull/579))
- `325cc7c4`: refactor(Logic): rename & refactor ([#597](https://github.com/FormalizedFormalLogic/Foundation/pull/597))
- `7c23fc78`: add(Modal): `EMC` equals to `EMCK` ([#596](https://github.com/FormalizedFormalLogic/Foundation/pull/596))
- `87bb48ca`: add(Modal/Neighborhood): Soundness of `EK` and `EMK` ([#595](https://github.com/FormalizedFormalLogic/Foundation/pull/595))
- `05e54f4f`: add(IntFO): Heyting valued model ([#593](https://github.com/FormalizedFormalLogic/Foundation/pull/593))
- `9096b38a`: feat(IntFO): redefine Kripke model of intuitionistic first-order logic ([#591](https://github.com/FormalizedFormalLogic/Foundation/pull/591))
- `9f6fbe29`: add(Modal): Add `EMK` and syntactical analysis ([#590](https://github.com/FormalizedFormalLogic/Foundation/pull/590))
- `8eae9b15`: refactor(Neighborhood): Canonicity ([#589](https://github.com/FormalizedFormalLogic/Foundation/pull/589))
- `3a9556d5`: add(Modal/Algebra): Definitions of Magari algebra ([#195](https://github.com/FormalizedFormalLogic/Foundation/pull/195))
- `8c9d11bf`: docs(Book): Neighborhood filtration ([#585](https://github.com/FormalizedFormalLogic/Foundation/pull/585))
- `1840b19b`: docs: Fix fonts ([#588](https://github.com/FormalizedFormalLogic/Foundation/pull/588))
- `580bb22e`: add(Book): on G1 and G2 ([#586](https://github.com/FormalizedFormalLogic/Foundation/pull/586))
- `1807efa0`: chore: Update to `v4.24.0-rc1` ([#582](https://github.com/FormalizedFormalLogic/Foundation/pull/582))
- `3c96ded4`: rename: `goedel`/`Goedel` ↦ `gödel`/ `Gödel` ([#583](https://github.com/FormalizedFormalLogic/Foundation/pull/583))
- `4615adcf`: add(Modal/Neighborhood): FFP of `EN4`, `ENT4`, `EMNT4`, `EMCN4` ([#584](https://github.com/FormalizedFormalLogic/Foundation/pull/584))
- `8ac14dcb`: docs: Book by Verso ([#399](https://github.com/FormalizedFormalLogic/Foundation/pull/399))
- `835896e4`: ci: Fix CI trigger ([#581](https://github.com/FormalizedFormalLogic/Foundation/pull/581))
- `201c5092`: add(Modal/Neighborhood): Add some observations ([#577](https://github.com/FormalizedFormalLogic/Foundation/pull/577))
- `dfe9cc43`: add(FirstOrder/SetTheory): functions in `𝗭` ([#578](https://github.com/FormalizedFormalLogic/Foundation/pull/578))
- `f1acb057`: add(FirstOrder): ordinals in Zermelo set theoey ([#575](https://github.com/FormalizedFormalLogic/Foundation/pull/575))
- `201dd59f`: refactor(Modal/Neighborhood): Refactor ([#576](https://github.com/FormalizedFormalLogic/Foundation/pull/576))

# Call for Support

We have created an [Open Collective account](https://opencollective.com/formalizedformallogic).
(GitHub Sponsors is now pending.)

Currently, this project receives little to no financial support.
If you find our work valuable, we would greatly appreciate contributions to help sustain our OSS development efforts.
All supports received will be shared between the two current maintainers.
