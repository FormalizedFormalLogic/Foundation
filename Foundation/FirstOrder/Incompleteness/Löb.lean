module
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition

/-!
# Löb's Theorem
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityLogic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem löb_theorem : T ⊢ (T.standardProvability σ) ➝ σ → T ⊢ σ := T.standardProvability.loeb_theorm

theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ T.standardProvability (T.standardProvability σ ➝ σ) ➝ T.standardProvability σ := T.standardProvability.formalized_loeb_theorem σ

end LO.FirstOrder.Arithmetic
