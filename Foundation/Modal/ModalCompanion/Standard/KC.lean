module

public import Foundation.Logic.Embedding
public import Foundation.Modal.Boxdot.GL_Grz
public import Foundation.Modal.Kripke.Logic.GrzPoint2
public import Foundation.Modal.ModalCompanion.Standard.Basic
public import Foundation.Propositional.Kripke.Hilbert.KC

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke


namespace S4Point2

@[simp, grind .]
lemma gödelTranslated_axiomWLEM : Modal.S4Point2 ⊢ (Axioms.WLEM φ)ᵍ := by
  apply Complete.complete (𝓜 := FrameClass.S4Point2);
  rintro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;

  apply Modal.Formula.Kripke.Satisfies.or_def.mpr;
  by_contra! hC;
  rcases hC with ⟨h₁, h₂⟩;

  replace h₁ := Modal.Formula.Kripke.Satisfies.dia_def.mp h₁;
  obtain ⟨y, Rxy, h₁⟩ := h₁;

  replace h₂ := Modal.Formula.Kripke.Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, h₂⟩ := h₂;

  obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rxy Rxz;
  apply h₂ u Rzu;
  apply Modal.gödelTranslated_persistency h₁ Ryu;

end S4Point2


namespace Propositional.KC

lemma provable_S4Point2_of_mem : φ ∈ Propositional.KC → Modal.S4Point2 ⊢ φᵍ := by
  apply Propositional.Hilbert.provable_gödelTranslated_of_mem_logic;
  rintro _ ⟨a, (⟨_, rfl⟩ | ⟨_, rfl⟩), rfl⟩ <;> simp;

theorem modalCompanion_S4Point2 : ModalCompanion Propositional.KC Modal.S4Point2 := by
  apply modalCompanion_via_kripkeSemantics (P := λ F => IsPiecewiseStronglyConvergent F);
  . apply provable_S4Point2_of_mem;
  . intro φ;
    apply Hilbert.KC.instKripkeComplete.complete;
  . rintro φ hφ F _ _;
    apply Modal.instSoundLogicNatFormulaFrameClassS4Point2S4Point2.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

lemma provable_GrzPoint2_of_mem : φ ∈ Propositional.KC → Modal.GrzPoint2 ⊢ φᵍ := fun h ↦ WeakerThan.pbl $ provable_S4Point2_of_mem h

theorem modalCompanion_GrzPoint2 : ModalCompanion Propositional.KC Modal.GrzPoint2 := by
  apply modalCompanion_via_kripkeSemantics (P := λ {κ} F => Finite κ ∧ IsPiecewiseStronglyConvergent F);
  . apply provable_GrzPoint2_of_mem;
  . intro φ;
    apply Hilbert.KC.instKripkeCompleteFinite.complete;
  . rintro φ hφ F _ ⟨_, _⟩;
    apply Modal.instSoundLogicNatFormulaFrameClassGrzPoint2Finite_GrzPoint2.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

end Propositional.KC

end LO

end
