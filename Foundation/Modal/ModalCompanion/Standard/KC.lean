module

public import Foundation.Modal.ModalCompanion.Standard.Int
public import Foundation.Modal.Kripke.Logic.GrzPoint2
public import Foundation.Propositional.Kripke.Logic.KC

@[expose] public section

namespace LO.Propositional

def Substitution.toModal (s : Propositional.Substitution α) : Modal.Substitution (α) := λ x => (s x).toModalFormula
instance : Coe (Propositional.Substitution α) (Modal.Substitution α) := ⟨Substitution.toModal⟩

end LO.Propositional


namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

namespace S4Point2

open Formula.Kripke in
lemma gödelTranslated_axiomWLEM : Modal.S4Point2 ⊢ □(∼φᵍ) ⋎ □(∼□(∼φᵍ)) := by
  suffices Modal.S4Point2 ⊢ □(∼(□φᵍ)) ⋎ □(∼□(∼□(φᵍ))) by
    apply A!_replace this;
    . apply axiomK'!;
      apply nec!;
      apply contra!;
      exact gödelTranslated_axiomTc;
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

instance : Entailment.HasAxiomPoint2 Propositional.KC.smallestMC where
  Point2 φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst (L := Propositional.KC.smallestMC) (φ := Modal.Axioms.Point2 (.atom 0)) (s := λ a => φ);
    have : Propositional.KC.smallestMC ⊢ □(∼□(.atom 0)) ⋎ □(∼□(∼□(.atom 0))) := by
      apply Logic.sumNormal.mem₂!;
      use Axioms.WLEM (.atom 0);
      constructor;
      . apply Propositional.Logic.iff_provable.mp;
        simp;
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
        apply Std.Refl.refl;

instance : Modal.S4Point2 ≊ Propositional.KC.smallestMC := by
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
    | subst ihφ => apply Logic.subst _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_gödelTranslated_of_provable ?_ (Propositional.Logic.iff_provable.mpr hφ);
      rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
      . simp;
      . exact S4Point2.gödelTranslated_axiomWLEM;

lemma eq_smallestMC_of_KC : Modal.S4Point2 = Propositional.KC.smallestMC := Logic.eq_of_equiv

instance : Sound Propositional.KC.smallestMC FrameClass.S4Point2 := Kripke.sound_frameClass_of_equiv Modal.S4Point2 Propositional.KC.smallestMC

instance modalCompanion_KC_S4Point2 : ModalCompanion Propositional.KC Modal.S4Point2 := by
  apply eq_smallestMC_of_KC ▸ Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := Propositional.KC)
    (IC := Propositional.Kripke.FrameClass.KC)
    (MC := Modal.Kripke.FrameClass.S4Point2)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end S4Point2


instance : Propositional.KC.smallestMC ⪯ Modal.GrzPoint2 := calc
  _ ≊ Modal.S4Point2  := by symm; infer_instance;
  _ ⪯ Modal.GrzPoint2 := inferInstance


namespace GrzPoint2

instance : Modal.GrzPoint2 ≊ Propositional.KC.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := Propositional.KC.smallestMC); simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Logic.subst _ ih;
    | nec ih => apply nec! ih;
    | mem₁ h => apply WeakerThan.pbl h;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

lemma is_largestMC_of_KC : Modal.GrzPoint2 = Propositional.KC.largestMC := Logic.eq_of_equiv

instance : Sound Propositional.KC.largestMC FrameClass.finite_GrzPoint2 := Kripke.sound_frameClass_of_equiv Modal.GrzPoint2 Propositional.KC.largestMC

instance : ModalCompanion Propositional.KC Modal.GrzPoint2 := by
  apply is_largestMC_of_KC ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_KC
    FrameClass.finite_GrzPoint2
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {}

end GrzPoint2

end LO.Modal
end
