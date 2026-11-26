module

public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.R0.Undecidability

/-!
# Church's undecidability theorem

Provability in pure first-order logic is undecidable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

section PeanoMinusReduction

/-- Provability in pure first-order logic, i.e. provability from the empty theory, is
undecidable. -/
theorem undecidability_first_order_logic :
    ¬ComputablePred (· ∈ (∅ : ArithmeticTheory).theory) := fun hC ↦ by
  have hImpIntro : Computable fun σ : ArithmeticSentence ↦ PeanoMinus.finite.toFinset.conj 🡒 σ :=
    let c := Encodable.encode (∼PeanoMinus.finite.toFinset.conj : ArithmeticSentence)
    computable_iff_sigma1_simulate (f := fun e ↦ ⟪5, c, e⟫ + 1) (by definability) fun σ ↦ by
      simp [nat_pair_eq, c, Semiformula.imp_eq, Semiformula.encode_or,
        ← Semiformula.encode_eq_toNat]
  apply R0.undecidable_of_consistent 𝗣𝗔⁻
  constructor
  apply (ComputablePred.computable_of_manyOneReducible (ManyOneReducible.mk _ hImpIntro) hC).of_eq
  intro σ
  change (∅ : ArithmeticTheory) ⊢ _ ↔ 𝗣𝗔⁻ ⊢ σ
  rw [Entailment.Equiv.iff.mp PeanoMinus.equiv_singleton_finiteConj σ, ← insert_empty_eq]
  exact Entailment.deduction_iff.symm

end PeanoMinusReduction

end FFL.FirstOrder.Arithmetic

end
