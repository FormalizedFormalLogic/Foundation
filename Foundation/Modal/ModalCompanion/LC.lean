import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Boxdot.GLPoint3_GrzPoint3
import Foundation.Propositional.Kripke.Logic.LC

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom goedelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

section S4Point3

lemma S4Point3.goedelTranslated_axiomDummett : Hilbert.S4Point3 ⊢! □(□ψᵍ ➝ χᵍ) ➝ □(ψᵍ ➝ χᵍ) := by
  apply axiomK'!;
  apply nec!;
  apply C!_swap;
  apply deduct'!;
  apply deduct!;
  have h₁ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ ➝ □ψᵍ := of'! $ goedelTranslated_axiomTc;
  have h₂ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ := by_axm!;
  have h₃ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! □ψᵍ ➝ χᵍ := by_axm!;
  exact h₃ ⨀ (h₁ ⨀ h₂);

@[simp]
lemma S4.CCLL_CCL : Modal.S4 ⊢! □(□φ ➝ □ψ) ➝ □(□φ ➝ ψ) := by
  apply Complete.complete (𝓜 := FrameClass.S4);
  rintro F ⟨_, _⟩ V x h₁ y Rxy h₂;
  apply @h₁ y Rxy h₂;
  apply IsRefl.refl;

namespace Logic

instance : Entailment.S4 Modal.S4 where

instance : Entailment.HasAxiomPoint3 (smallestMC 𝐋𝐂) where
  Point3 φ ψ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst! (L := (smallestMC 𝐋𝐂)) (φ := Modal.Axioms.Point3 (.atom 0) (.atom 1)) (s := λ a => match a with | 0 => φ | 1 => ψ | _ => .atom a);
    have : (smallestMC 𝐋𝐂) ⊢! □(□.atom 0 ➝ □.atom 1) ⋎ □(□.atom 1 ➝ □.atom 0) := by
      apply Logic.sumNormal.mem₂!;
      use Axioms.Dummett (.atom 0) (.atom 1);
      constructor;
      . simp [theory];
      . tauto;
    apply ?_ ⨀ this;
    apply CAA!_of_C!_of_C! <;>
    . apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
      simp;

lemma S4Point3.is_smallestMC_of_LC : Modal.S4Point3 = (smallestMC 𝐋𝐂) := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    simp only [Hilbert.Normal.iff_logic_provable_provable] at hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | subst ihφ => apply subst! _ ihφ;
    | mem₂ h =>
      apply Hilbert.Normal.iff_logic_provable_provable.mpr;
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_goedelTranslated_of_provable Hilbert.LC Hilbert.S4Point3;
      . rintro _ ⟨_, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩;
        . simp;
        . apply A!_replace axiomPoint3! <;>
          apply S4Point3.goedelTranslated_axiomDummett;
      . simpa [theory] using hφ;

instance : Sound (smallestMC 𝐋𝐂) FrameClass.S4Point3 := by
  rw [←Logic.S4Point3.is_smallestMC_of_LC];
  infer_instance;

instance modalCompanion_LC_S4Point3 : ModalCompanion 𝐋𝐂 Modal.S4Point3 := by
  rw [Logic.S4Point3.is_smallestMC_of_LC];
  apply Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.LC)
    (MC := Modal.Kripke.FrameClass.S4Point3)
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end Logic

end S4Point3


section GrzPoint3

lemma Logic.gGrzPoint3_of_LC : 𝐋𝐂 ⊢! φ → Modal.GrzPoint3 ⊢! φᵍ := by
  intro h;
  apply WeakerThan.pbl $ modalCompanion_LC_S4Point3.companion.mp h;

lemma Logic.GrzPoint3.is_largestMC_of_LC : Modal.GrzPoint3 = (Logic.largestMC 𝐋𝐂) := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    simp only [Hilbert.Normal.iff_logic_provable_provable] at hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := (smallestMC 𝐋𝐂));
        simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl $ Logic.S4Point3.is_smallestMC_of_LC ▸ h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : Sound (Logic.largestMC 𝐋𝐂) { F : Frame | F.IsFiniteGrzPoint3' } := by
  rw [←Logic.GrzPoint3.is_largestMC_of_LC];
  infer_instance;

instance modalCompanion_LC_GrzPoint3 : ModalCompanion 𝐋𝐂 Modal.GrzPoint3 := by
  rw [Logic.GrzPoint3.is_largestMC_of_LC];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_LC)
    (MC := { F : Frame | F.IsFiniteGrzPoint3' })
    (by intro F hF; simp_all only [Set.mem_setOf_eq]; exact {})

end GrzPoint3


section boxdot

theorem embedding_LC_GLPoint3 {φ : Propositional.Formula ℕ} : 𝐋𝐂 ⊢! φ ↔ Modal.GLPoint3 ⊢! φᵍᵇ :=
  Iff.trans modalCompanion_LC_GrzPoint3.companion iff_boxdot_GLPoint3_GrzPoint3.symm

end boxdot


end LO.Modal
