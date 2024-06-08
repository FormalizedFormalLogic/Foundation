# Modal Companion

## Gödel-McKensey-Tarski Theorem

Through a translation called _Gödel Translation_ from propositional logic formula to modal logic formula, intuitionistic logic $\bf Int$ can be embedded into $\bf S4$. (This theorem is known as _Gödel-McKensey-Tarski Theorem_.)

```lean
def GoedelTranslation : Superintuitionistic.Formula α → Formula α

postfix:75 "ᵍ" => GoedelTranslation

theorem provable_efq_iff_provable_S4
  {p : Superintuitionistic.Formula α}
  : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ
```
- [LO.Modal.Standard.provable_efq_iff_provable_S4](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/ModalCompanion.html#LO.Modal.Standard.provable_efq_iff_provable_S4)

## Modal Companion

The generalized version of this relationship is called _Modal Companion_. $(\bf Int,S4)$ has modal companion.

```lean
class ModalCompanion (i𝓓 : Superintuitionistic.DeductionParameter α) (m𝓓 : Modal.Standard.DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, i𝓓 ⊢! p ↔ m𝓓 ⊢! pᵍ

instance : ModalCompanion 𝐈𝐧𝐭 𝐒𝟒
```
- [LO.Modal.Standard.instModalCompanionIntuitionisticS4](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/ModalCompanion.html#LO.Modal.Standard.instModalCompanionIntuitionisticS4)
