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
def Logic.IsProvabilityLogic (L : Modal.Logic ℕ) (T U : ArithmeticTheory) [T.Δ₁] := ∀ A, L ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A

end Modal


namespace FirstOrder

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} [T.Δ₁] {A : Modal.Formula ℕ}

/-- Provability Logic of `T` relative to metatheory `U` -/
def provabilityLogicOn (T U : ArithmeticTheory) [T.Δ₁] : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢ f A}

@[simp, grind .]
lemma isProvabilityLogic_provabilityLogicOn : (T.provabilityLogicOn U).IsProvabilityLogic T U := by
  simp [Modal.Logic.IsProvabilityLogic, provabilityLogicOn];
  grind;

@[grind =]
lemma provabilityLogicOn.provable_iff : (T.provabilityLogicOn U) ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A := by
  simp [Modal.Logic.iff_provable, provabilityLogicOn]

instance : Entailment.Łukasiewicz (T.provabilityLogicOn U) where
  mdp := by
    rintro A B ⟨hA⟩ ⟨hB⟩;
    constructor;
    simp only [←Modal.Logic.iff_provable, provabilityLogicOn.provable_iff] at hA hB ⊢;
    intro f;
    replace hA : U ⊢ f A ➝ f B := hA f;
    replace hB : U ⊢ f A := hB f;
    cl_prover [hA, hB];
  implyK {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply provabilityLogicOn.provable_iff.mpr;
    simp;
  implyS {_ _ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply provabilityLogicOn.provable_iff.mpr;
    simp;
  elimContra {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply provabilityLogicOn.provable_iff.mpr;
    intro f;
    dsimp [ProvabilityLogic.Realization.interpret];
    cl_prover;

instance : Entailment.Cl (T.provabilityLogicOn U) where

end ArithmeticTheory

end FirstOrder

end LO

end
