import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.GrzPoint2
import Foundation.Propositional.Kripke.Logic.KC

namespace LO.Propositional

def Substitution.toModal (s : Propositional.Substitution α) : Modal.Substitution (α) := λ x => (s x).toModalFormula
instance : Coe (Propositional.Substitution α) (Modal.Substitution α) := ⟨Substitution.toModal⟩

end LO.Propositional


namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom goedelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

section S4Point2

open Formula.Kripke in
lemma Logic.S4Point2.goedelTranslated_axiomWLEM : Modal.S4Point2 ⊢! □(∼φᵍ) ⋎ □(∼□(∼φᵍ)) := by
  suffices Modal.S4Point2 ⊢! □(∼(□φᵍ)) ⋎ □(∼□(∼□(φᵍ))) by
    apply A!_replace this;
    . apply axiomK'!;
      apply nec!;
      apply contra!;
      exact goedelTranslated_axiomTc;
    . apply axiomK'!;
      apply nec!;
      apply contra!;
      apply axiomK'!;
      apply nec!;
      apply contra!;
      exact axiomT!
  apply Complete.complete (𝓜 := FrameClass.S4Point2);
  rintro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;

  apply Formula.Kripke.Satisfies.or_def.mpr;
  by_contra! hC;
  rcases hC with ⟨h₁, h₂⟩;

  replace h₁ := Formula.Kripke.Satisfies.dia_def.mp h₁;
  obtain ⟨y, Rxy, h₁⟩ := h₁;

  replace h₂ := Formula.Kripke.Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, h₂⟩ := h₂;

  obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rxy Rxz;

  have := Formula.Kripke.Satisfies.box_def.not.mp $ h₂ u Rzu;
  push_neg at this;
  obtain ⟨v, Ruv, h⟩ := this;

  have := h₁ v $ IsTrans.trans _ _ _ Ryu Ruv
  contradiction;

namespace Logic

instance : Entailment.HasAxiomPoint2 (smallestMC 𝐊𝐂) where
  Point2 φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst! (L := (smallestMC 𝐊𝐂)) (φ := Modal.Axioms.Point2 (.atom 0)) (s := λ a => φ);
    have : (smallestMC 𝐊𝐂) ⊢! □(∼□(.atom 0)) ⋎ □(∼□(∼□(.atom 0))) := by
      apply Logic.sumNormal.mem₂!;
      use Axioms.WeakLEM (.atom 0);
      constructor;
      . simp [theory];
      . tauto;
    apply ?_ ⨀ this;
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
    apply Complete.complete (𝓜 := FrameClass.S4);
    rintro F ⟨_, _⟩ V x h₁ h₂ y Rxy;
    replace h₁ := Satisfies.or_def.mp h₁;
    replace h₂ := Satisfies.dia_def.mp h₂;
    obtain ⟨z, Rxz, h₂⟩ := h₂;

    rcases h₁ with (h₁ | h₁);
    . have := h₁ z Rxz;
      contradiction;
    . have := Satisfies.box_def.not.mp $ Satisfies.not_def.mp $ h₁ y Rxy
      push_neg at this;
      obtain ⟨u, Ryu, h⟩ := this;
      apply Satisfies.dia_def.mpr;
      use u;
      constructor;
      . assumption;
      . apply Satisfies.negneg_def.mp h u
        apply IsRefl.refl;

lemma S4Point2.is_smallestMC_of_KC : Modal.S4Point2 = (smallestMC 𝐊𝐂) := by
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
      apply provable_goedelTranslated_of_provable Hilbert.KC Modal.S4Point2;
      . rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
        . simp;
        . simpa using Logic.S4Point2.goedelTranslated_axiomWLEM;
      . simpa [theory] using hφ;

instance : Sound (smallestMC 𝐊𝐂) FrameClass.S4Point2 := by
  rw [←Logic.S4Point2.is_smallestMC_of_KC];
  infer_instance;

instance modalCompanion_KC_S4Point2 : ModalCompanion 𝐊𝐂 Modal.S4Point2 := by
  rw [Logic.S4Point2.is_smallestMC_of_KC];
  apply Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := 𝐊𝐂)
    (IC := Propositional.Kripke.FrameClass.KC)
    (MC := Modal.Kripke.FrameClass.S4Point2)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {};

end Logic

end S4Point2


section GrzPoint2

lemma Logic.gGrzPoint2_of_KC : 𝐊𝐂 ⊢! φ → Modal.GrzPoint2 ⊢! φᵍ := by
  intro h;
  apply WeakerThan.pbl $ modalCompanion_KC_S4Point2.companion.mp h;

lemma Logic.GrzPoint2.is_largestMC_of_KC : Modal.GrzPoint2 = (Logic.largestMC 𝐊𝐂) := by
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
      . apply WeakerThan.pbl (𝓢 := (smallestMC 𝐊𝐂));
        simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl $ Logic.S4Point2.is_smallestMC_of_KC ▸ h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : Sound (Logic.largestMC 𝐊𝐂) FrameClass.finite_GrzPoint2 := by
  rw [←Logic.GrzPoint2.is_largestMC_of_KC];
  infer_instance;

instance modalCompanion_KC_GrzPoint2 : ModalCompanion 𝐊𝐂 Modal.GrzPoint2 := by
  rw [Logic.GrzPoint2.is_largestMC_of_KC];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_KC
    Modal.Kripke.FrameClass.finite_GrzPoint2
    $ by intro F hF; simp_all only [Set.mem_setOf_eq]; exact {}

end GrzPoint2


end LO.Modal
