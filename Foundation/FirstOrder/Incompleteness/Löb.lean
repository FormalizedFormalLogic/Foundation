module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition

@[expose] public section
/-!
# Löb's Theorem
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityAbstraction

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem löb_theorem : T ⊢ (T.standardProvability σ) ➝ σ → T ⊢ σ := ProvabilityAbstraction.löb_theorm (𝔅 := T.standardProvability)

theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ T.standardProvability (T.standardProvability σ ➝ σ) ➝ T.standardProvability σ := ProvabilityAbstraction.formalized_löb_theorem (𝔅 := T.standardProvability )

end LO.FirstOrder.Arithmetic
