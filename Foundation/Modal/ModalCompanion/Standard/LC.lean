module

public import Foundation.Logic.Embedding
public import Foundation.Modal.Boxdot.GLPoint3_GrzPoint3
public import Foundation.Modal.Kripke.Logic.GrzPoint3
public import Foundation.Modal.ModalCompanion.Standard.Basic
public import Foundation.Propositional.Kripke.Hilbert.LC

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke


namespace S4Point3

@[simp, grind .]
lemma gödelTranslated_axiomDummett : Modal.S4Point3 ⊢ (Axioms.Dummett φ ψ)ᵍ := by
  apply Complete.complete (𝓜 := FrameClass.S4Point3);
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Modal.Formula.Kripke.Satisfies.or_def.mpr;
  by_contra! hC;
  rcases hC with ⟨h₁, h₂⟩;
  obtain ⟨y, Rxy, hy⟩ := Modal.Formula.Kripke.Satisfies.not_box_def.mp h₁;
  obtain ⟨hyφ, hyψ⟩ := Modal.Formula.Kripke.Satisfies.not_imp_def.mp hy;
  obtain ⟨z, Rxz, hz⟩ := Modal.Formula.Kripke.Satisfies.not_box_def.mp h₂;
  obtain ⟨hzφ, hzψ⟩ := Modal.Formula.Kripke.Satisfies.not_imp_def.mp hz;
  rcases F.ps_connected Rxy Rxz with (Ryz | Rzy);
  . apply hzψ $ Modal.gödelTranslated_persistency hyφ Ryz;
  . apply hyψ $ Modal.gödelTranslated_persistency hzφ Rzy;

end S4Point3


namespace Propositional.LC

lemma provable_S4Point3_of_mem : φ ∈ Propositional.LC → Modal.S4Point3 ⊢ φᵍ := by
  apply Propositional.Hilbert.provable_gödelTranslated_of_mem_logic;
  rintro _ ⟨a, (⟨_, rfl⟩ | ⟨_, _, rfl⟩), rfl⟩ <;> simp;

theorem modalCompanion_S4Point3 : ModalCompanion Propositional.LC Modal.S4Point3 := by
  apply modalCompanion_via_kripkeSemantics (P := λ F => IsPiecewiseStronglyConnected F);
  . apply provable_S4Point3_of_mem;
  . intro φ;
    apply Hilbert.LC.instKripkeComplete.complete;
  . rintro φ hφ F _ _;
    apply Modal.instSoundLogicNatFormulaFrameClassS4Point3S4Point3.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

lemma provable_GrzPoint3_of_mem : φ ∈ Propositional.LC → Modal.GrzPoint3 ⊢ φᵍ := fun h ↦ WeakerThan.pbl $ provable_S4Point3_of_mem h

theorem modalCompanion_GrzPoint3 : ModalCompanion Propositional.LC Modal.GrzPoint3 := by
  apply modalCompanion_via_kripkeSemantics (P := λ {κ} F => Finite κ ∧ IsPiecewiseStronglyConnected F);
  . apply provable_GrzPoint3_of_mem;
  . intro φ;
    apply Hilbert.LC.instKripkeCompleteFinite.complete;
  . rintro φ hφ F _ ⟨_, _⟩;
    apply Modal.instSoundLogicNatFormulaSetFrameGrzPoint3SetOfIsFiniteGrzPoint3'.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

theorem boxdotModalCompanion_LC : ∀ φ, φ ∈ Propositional.LC ↔ Modal.GLPoint3 ⊢ φᵍᵇ :=
  λ _ => Iff.trans modalCompanion_GrzPoint3 $ Modal.iff_boxdot_GLPoint3_GrzPoint3.symm

end Propositional.LC

end LO

end
