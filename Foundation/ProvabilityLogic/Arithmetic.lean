module

public import Foundation.ProvabilityLogic.Realization
/-!
# Provability logic of arithmetic theory
-/

@[expose] public section

namespace LO

open FirstOrder

namespace Modal

/-- `L` is provability logic of `U` on `T` -/
abbrev Logic.IsProvabilityLogicOf (L : Modal.Logic ℕ) (T U : ArithmeticTheory) [T.Δ₁] := ∀ A ∈ L, ∀ f : T.StandardRealization, U ⊢ f A

/-- `L` is provability logic of `U` on `T` -/
abbrev Logic.IsProvabilityLogic (L : Modal.Logic ℕ) : Prop := ∃ T : ArithmeticTheory, ∃ TΔ₁ : T.Δ₁, ∃ U, @Logic.IsProvabilityLogicOf L T U TΔ₁

/-- Provability Logics of `U` on `T` -/
abbrev ProvabilityLogic := { L : Modal.Logic ℕ // Logic.IsProvabilityLogic L }

end Modal


namespace FirstOrder

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} [T.Δ₁] {A : Modal.Formula ℕ}

/-- Provability Logic of `U` on `T` -/
def ProvabilityLogicOf (T U : ArithmeticTheory) [T.Δ₁] : Modal.ProvabilityLogic := ⟨{A | ∀ f : T.StandardRealization, U ⊢ f A}, ⟨T, inferInstance, U, λ _ h f => h f⟩⟩

@[grind =]
lemma ProvabilityLogicOf.provable_iff : (T.ProvabilityLogicOf U).1 ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A := by simp [Modal.Logic.iff_provable, ProvabilityLogicOf]

instance : Entailment.Łukasiewicz (T.ProvabilityLogicOf U).1 where
  mdp := by
    rintro A B ⟨hA⟩ ⟨hB⟩;
    constructor;
    simp only [←Modal.Logic.iff_provable, ProvabilityLogicOf.provable_iff] at hA hB ⊢;
    intro f;
    replace hA : U ⊢ f A ➝ f B := hA f;
    replace hB : U ⊢ f A := hB f;
    cl_prover [hA, hB];
  implyK {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogicOf.provable_iff.mpr;
    simp;
  implyS {_ _ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogicOf.provable_iff.mpr;
    simp;
  elimContra {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply ProvabilityLogicOf.provable_iff.mpr;
    intro f;
    dsimp [ProvabilityLogic.Realization.interpret];
    cl_prover;

instance : Entailment.Cl (T.ProvabilityLogicOf U).1 where

end ArithmeticTheory

end FirstOrder

end LO

end
