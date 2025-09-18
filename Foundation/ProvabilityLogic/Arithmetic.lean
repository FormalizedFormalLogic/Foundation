import Foundation.ProvabilityLogic.Realization
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Provability logic of arithmetic theory
-/

namespace LO.FirstOrder

variable (T U : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.ProvabilityLogic : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢!. f A}

variable {T U} {A B C : Modal.Formula ℕ}

namespace ArithmeticTheory.ProvabilityLogic

lemma provable_iff :
    ProvabilityLogic T U ⊢! A ↔ ∀ f : T.StandardRealization, U ⊢!. f A := by
  simp [ArithmeticTheory.ProvabilityLogic]

instance : Entailment.Lukasiewicz (ProvabilityLogic T U) where
  mdp := by
    rintro A B ⟨hA⟩ ⟨hB⟩;
    constructor;
    simp only [←Modal.Logic.iff_provable, ProvabilityLogic.provable_iff] at hA hB ⊢;
    intro f;
    replace hA : U ⊢!. f A ➝ f B := hA f;
    replace hB : U ⊢!. f A := hB f;
    cl_prover [hA, hB];
  imply₁ A B := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    simp;
  imply₂ A B C := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    simp;
  elimContra A B := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    intro f;
    dsimp [ProvabilityLogic.Realization.interpret];
    cl_prover;

instance : Entailment.Cl (ProvabilityLogic T U) where

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
