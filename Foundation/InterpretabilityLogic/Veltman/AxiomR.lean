module

public import Foundation.InterpretabilityLogic.Veltman.Basic
public import Foundation.InterpretabilityLogic.Veltman.AxiomJ2
public import Foundation.InterpretabilityLogic.Veltman.Logic.IL
public import Mathlib.Tactic.TFAE

@[expose] public section

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
lemma Frame.HasAxiomR.of_validate_axiomP₀ [F.IsIL] (h : F ⊧ Axioms.P₀ (.atom 0) (.atom 1)) : F.HasAxiomR := by
  constructor;
  intro x y z u v Rxy Ryz Sxzu Ruv;
  have := @h (λ w a =>
    match a with
    | 0 => w = z
    | 1 => w = v
    | _ => False
  ) x ?_ y Rxy z Ryz ?_;
  . obtain ⟨w, hw₁, hw₂⟩ := this;
    simp [Satisfies] at hw₁ hw₂;
    grind;
  . suffices ∀ w, x ≺ w → w = z → ∃ z, w ≺[x] z ∧ z ≺ v by simpa [Satisfies];
    rintro w Rxw rfl;
    use u;
  . tauto;

open Hilbert.Basic in
lemma validate_axiomP₀_of_validate_axiomR [F.IsIL] (h : F ⊧ Axioms.R (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.P₀ φ ψ := by
  apply Hilbert.Basic.Veltman.soundness_frame (Ax := IL_R.axioms);
  . constructor;
    rintro φ hφ;
    rcases (by simpa using hφ) with (rfl | rfl | rfl | rfl | rfl | rfl);
    . assumption;
    . simp [validate_axiomJ5_of_J5]
    . simp [validate_axiomJ1_of_J1]
    . simp [validate_axiomJ2_of_HasAxiomJ2]
    . simp [validate_axiomJ3]
    . simp [validate_axiomJ4_of_HasAxiomJ4]
  . suffices InterpretabilityLogic.IL_R ⊢ Axioms.P₀ φ ψ by tauto;
    simp;

lemma TFAE_HasAxiomR [F.IsIL] : [
    F.HasAxiomR,
    F ⊧ Axioms.R (.atom 0) (.atom 1) (.atom 2),
    F ⊧ Axioms.P₀ (.atom 0) (.atom 1)
  ].TFAE := by
    tfae_have 1 → 2 := by apply validate_axiomR_of_HasAxiomR;
    tfae_have 2 → 3 := validate_axiomP₀_of_validate_axiomR;
    tfae_have 3 → 1 := Frame.HasAxiomR.of_validate_axiomP₀
    tfae_finish;

lemma Frame.HasAxiomR.of_validate_axiomR [F.IsIL] (h : F ⊧ Axioms.R (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomR := TFAE_HasAxiomR.out 1 0 |>.mp h

@[simp high, grind .]
lemma validate_axiomP₀_of_HasAxiomR [F.IsIL] [F.HasAxiomR] : F ⊧ Axioms.P₀ φ ψ := by
  have : F ⊧ Axioms.P₀ (.atom 0) (.atom 1) := TFAE_HasAxiomR.out 0 2 |>.mp (by infer_instance);
  apply ValidOnFrame.subst (s := λ n => match n with | 0 => φ | 1 => ψ | _ => ⊥) this;

end LO.InterpretabilityLogic.Veltman
end
