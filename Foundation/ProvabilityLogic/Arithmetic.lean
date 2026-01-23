import Foundation.ProvabilityLogic.Realization
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# Provability logic of arithmetic theory
-/

namespace LO.FirstOrder

variable (T U : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.ProvabilityLogic : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢ f A}

variable {T U} {A B C : Modal.Formula ℕ}

namespace ArithmeticTheory.ProvabilityLogic

@[grind =]
lemma provable_iff : ProvabilityLogic T U ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A := by
  simp [Modal.Logic.iff_provable, ArithmeticTheory.ProvabilityLogic]

instance : Entailment.Łukasiewicz (ProvabilityLogic T U) where
  mdp := by
    rintro A B ⟨hA⟩ ⟨hB⟩;
    constructor;
    simp only [←Modal.Logic.iff_provable, ProvabilityLogic.provable_iff] at hA hB ⊢;
    intro f;
    replace hA : U ⊢ f A ➝ f B := hA f;
    replace hB : U ⊢ f A := hB f;
    cl_prover [hA, hB];
  implyK {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    simp;
  implyS {_ _ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    simp;
  elimContra {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogic.provable_iff.mpr;
    intro f;
    dsimp [ProvabilityLogic.Realization.interpret];
    cl_prover;

instance : Entailment.Cl (ProvabilityLogic T U) where

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
