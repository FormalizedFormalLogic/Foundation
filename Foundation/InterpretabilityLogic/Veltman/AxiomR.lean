import Foundation.InterpretabilityLogic.Veltman.Basic
import Foundation.InterpretabilityLogic.Veltman.AxiomJ2
import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Mathlib.Tactic.TFAE

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomR (F : Frame) : Prop where
  S_R : ∀ {x y z u v: F.World}, x ≺ y → y ≺ z → z ≺[x] u → u ≺ v → z ≺[y] v
export HasAxiomR (S_R)

end Frame

@[simp high, grind .]
lemma validate_axiomR_of_HasAxiomR [F.IsIL] [F.HasAxiomR] : F ⊧ Axioms.R φ ψ χ := by
  intro V x h₁ y Rxy h₂;
  obtain ⟨z, Ryz, h₃, h₄⟩ := Satisfies.not_rhd_def.mp h₂;
  obtain ⟨u, Sxzu, h⟩ := h₁ z (F.trans Rxy Ryz) h₃;
  use u;
  constructor;
  . apply F.S_J2 ?_ Sxzu;
    apply F.S_J5 Rxy Ryz;
  . apply Satisfies.and_def.mpr;
    constructor;
    . assumption;
    . intro v Ruv;
      apply Satisfies.not_neg_def.mp $ h₄ v ?_;
      apply F.S_R Rxy Ryz Sxzu Ruv;

open Formula (atom) in
lemma Frame.HasAxiomR.of_validate_axiomR (h : F ⊧ Axioms.R (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomR := by
  constructor;
  intro x y z u v Rxy Ryz Sxzu Ruv;
  have := @h (λ w a =>
    match a with
    | 0 => w = z
    | 1 => w = u
    | 2 => z ≺[y] w
    | _ => False
  ) x ?_ y Rxy ?_;
  . simp [Satisfies] at this;
    grind;
  . intro w Rxw;
    suffices w = z → w ≺[x] u by simpa [Satisfies];
    grind;
  . apply Satisfies.not_rhd_def.mpr;
    simpa [Satisfies];

end LO.InterpretabilityLogic.Veltman
