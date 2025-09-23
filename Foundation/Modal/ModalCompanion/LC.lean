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

@[simp]
lemma S4.CCLL_CCL : Modal.S4 ⊢! □(□φ ➝ □ψ) ➝ □(□φ ➝ ψ) := by
  apply Complete.complete (𝓜 := FrameClass.S4);
  rintro F ⟨_, _⟩ V x h₁ y Rxy h₂;
  apply @h₁ y Rxy h₂;
  apply IsRefl.refl;

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

namespace S4Point3

lemma goedelTranslated_axiomDummett : Modal.S4Point3 ⊢! □(□ψᵍ ➝ χᵍ) ➝ □(ψᵍ ➝ χᵍ) := by
  apply axiomK'!;
  apply nec!;
  apply C!_swap;
  apply deduct'!;
  apply deduct!;
  have h₁ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Modal.S4Point3]! ψᵍ ➝ □ψᵍ := of'! $ goedelTranslated_axiomTc;
  have h₂ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Modal.S4Point3]! ψᵍ := by_axm!;
  have h₃ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Modal.S4Point3]! □ψᵍ ➝ χᵍ := by_axm!;
  exact h₃ ⨀ (h₁ ⨀ h₂);

instance : Modal.S4Point3 ≊ 𝐋𝐂.smallestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | subst ihφ => apply Logic.subst! _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_goedelTranslated_of_provable 𝐋𝐂 Modal.S4Point3;
      . rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
        . simp;
        . apply A!_replace axiomPoint3! <;>
          apply S4Point3.goedelTranslated_axiomDummett;
      . simpa [theory] using hφ;

lemma eq_smallestMC_of_KC : Modal.S4Point3 = 𝐋𝐂.smallestMC := Logic.eq_of_equiv

instance : Sound 𝐋𝐂.smallestMC FrameClass.S4Point3 := Kripke.sound_frameClass_of_equiv Modal.S4Point3 𝐋𝐂.smallestMC

instance : ModalCompanion 𝐋𝐂 Modal.S4Point3 := by
  apply eq_smallestMC_of_KC ▸ Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := 𝐋𝐂)
    (IC := Propositional.Kripke.FrameClass.LC)
    (MC := Modal.Kripke.FrameClass.S4Point3)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end S4Point3


instance : 𝐋𝐂.smallestMC ⪯ Modal.GrzPoint3 := calc
  _ ≊ Modal.S4Point3  := by symm; infer_instance;
  _ ⪯ Modal.GrzPoint3 := inferInstance



section GrzPoint3

instance : Modal.GrzPoint3 ≊ 𝐋𝐂.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := 𝐋𝐂.smallestMC); simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Logic.subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₁ h => apply WeakerThan.pbl h;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

lemma is_largestMC_of_LC : Modal.GrzPoint3 = 𝐋𝐂.largestMC := Logic.eq_of_equiv

instance : Sound 𝐋𝐂.largestMC FrameClass.finite_GrzPoint3 := Kripke.sound_frameClass_of_equiv Modal.GrzPoint3 𝐋𝐂.largestMC

instance : ModalCompanion 𝐋𝐂 Modal.GrzPoint3 := by
  apply is_largestMC_of_LC ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_LC
    ({ F : Frame | F.IsFiniteGrzPoint3' })
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {}

end GrzPoint3


section boxdot

theorem embedding_LC_GLPoint3 {φ : Propositional.Formula ℕ} : 𝐋𝐂 ⊢! φ ↔ Modal.GLPoint3 ⊢! φᵍᵇ :=
  Iff.trans ModalCompanion.companion iff_boxdot_GLPoint3_GrzPoint3.symm

end boxdot


end LO.Modal
