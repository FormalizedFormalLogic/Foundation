module

public import Foundation.FirstOrder.Incompleteness.StandardProvability

@[expose] public section
/-!
# Löb's Theorem
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment Bootstrapping ProvabilityAbstraction

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem löb_theorem : T ⊢ provabilityPred T σ 🡒 σ → T ⊢ σ :=
  ProvabilityAbstraction.löb_theorem (𝔅 := T.standardProvability)

theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ provabilityPred T (provabilityPred T σ 🡒 σ) 🡒 provabilityPred T σ :=
  ProvabilityAbstraction.formalized_löb_theorem (𝔅 := T.standardProvability)

end LO.FirstOrder.Arithmetic
