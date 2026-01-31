module

public import Foundation.ProvabilityLogic.Realization
/-!
# Provability logic of arithmetic theory
-/

@[expose] public section

namespace LO

open FirstOrder

namespace Modal

/-- `L` is provability logic of `T` relative to metatheory `U` -/
def Logic.IsProvabilityLogicOf (L : Modal.Logic ℕ) (T U : ArithmeticTheory) [T.Δ₁] := ∀ A, L ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A

end Modal


namespace FirstOrder

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} [T.Δ₁] {A : Modal.Formula ℕ}

/-- Provability Logic of `T` relative to metatheory `U` -/
def ProvabilityLogicOf (T U : ArithmeticTheory) [T.Δ₁] : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢ f A}

@[simp, grind .]
lemma isProvabilityLogic_ProvabilityLogicOf : (ProvabilityLogicOf T U).IsProvabilityLogicOf T U := by
  simp [Modal.Logic.IsProvabilityLogicOf, ProvabilityLogicOf];
  grind;

@[grind =]
lemma ProvabilityLogicOf.provable_iff : (T.ProvabilityLogicOf U) ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A := by
  simp [Modal.Logic.iff_provable, ProvabilityLogicOf]

instance : Entailment.Łukasiewicz (T.ProvabilityLogicOf U) where
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

instance : Entailment.Cl (T.ProvabilityLogicOf U) where

end ArithmeticTheory

end FirstOrder

end LO

end
