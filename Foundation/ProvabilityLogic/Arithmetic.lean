import Foundation.ProvabilityLogic.Realization
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Provability logic of arithmetic theory
-/

namespace LO.FirstOrder

variable (T U : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.ProvabilityLogic : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢!. f A}

variable {T U}

namespace ArithmeticTheory.ProvabilityLogic

lemma provable_iff :
    ProvabilityLogic T U ⊢! A ↔ ∀ f : T.StandardRealization, U ⊢!. f A := by
  simp [ArithmeticTheory.ProvabilityLogic]

lemma mdp : ProvabilityLogic T U ⊢! A ➝ B → ProvabilityLogic T U ⊢! A → ProvabilityLogic T U ⊢! B := by
  simp only [provable_iff];
  intro hAB hA f;
  replace hAB : U ⊢!. f A ➝ f B := hAB f;
  replace hA : U ⊢!. f A := hA f;
  cl_prover [hAB, hA]

instance : Entailment.ModusPonens (ProvabilityLogic T U) := ⟨by
  rintro A B ⟨hA⟩ ⟨hB⟩;
  constructor;
  simp only [←Modal.Logic.iff_provable] at hA hB ⊢;
  apply mdp hA hB;
⟩

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
