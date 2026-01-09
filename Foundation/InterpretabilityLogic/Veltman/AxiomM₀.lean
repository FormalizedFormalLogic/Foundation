module
import Foundation.InterpretabilityLogic.Veltman.Basic
import Foundation.InterpretabilityLogic.Veltman.Logic.IL

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomM₀ (F : Frame) : Prop where
  S_M₀ : ∀ {a b c d e : F.World}, a ≺ b → b ≺ c → c ≺[a] d → d ≺ e → b ≺ e
export HasAxiomM₀ (S_M₀)

end Frame

@[simp high, grind .]
lemma validate_axiomM₀_of_HasAxiomM₀ [F.IsIL] [F.HasAxiomM₀] : F ⊧ Axioms.M₀ φ ψ χ := by
  intro V x h₁ y Rxy h₂;
  have ⟨h₂₁, h₂₂⟩ := Satisfies.and_def.mp h₂; clear h₂;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp h₂₁; clear h₂₁;
  obtain ⟨u, Sxzu, hu⟩ := h₁ z (F.trans Rxy Ryz) hz;
  use u;
  constructor;
  . apply F.S_J2 ?_ Sxzu;
    apply F.S_J5 Rxy Ryz;
  . apply Satisfies.and_def.mpr;
    constructor;
    . tauto;
    . intro w Ruw;
      apply h₂₂;
      apply F.S_M₀ Rxy Ryz Sxzu Ruw;

open Formula (atom) in
lemma Frame.HasAxiomM₀.of_validate_axiomM₀ [F.IsIL] (h : F ⊧ Axioms.M₀ (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomM₀ := by
  constructor;
  intro a b c d e Rab Rbc Sacd Rde;
  have ⟨x, Sabx, h₁⟩ := @h (λ w p => match p with | 0 => c = w | 1 => d = w | 2 => b ≺ w | _ => False) a ?_ b ?_ ?_;
  . obtain ⟨rfl, h₂⟩ := Satisfies.and_def.mp h₁;
    apply h₂ _ Rde;
  . rintro _ Rac rfl;
    use d;
    tauto;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . apply Satisfies.dia_def.mpr;
      use c;
      constructor;
      . assumption;
      . tauto;
    . intro y Rby;
      tauto;

end LO.InterpretabilityLogic.Veltman
