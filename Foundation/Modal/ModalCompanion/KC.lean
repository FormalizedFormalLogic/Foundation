import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.GrzPoint2

namespace LO.Propositional

def Substitution.toModal (s : Propositional.Substitution α) : Modal.Substitution (α) := λ x => (s x).toModalFormula
instance : Coe (Propositional.Substitution α) (Modal.Substitution α) := ⟨Substitution.toModal⟩

end LO.Propositional


namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke


section S4Point2

open Formula.Kripke in
lemma Hilbert.S4Point2.goedelTranslated_axiomWLEM : Hilbert.S4Point2 ⊢! □(∼φᵍ) ⋎ □(∼□(∼φᵍ)) := by
  suffices Hilbert.S4Point2 ⊢! □(∼(□φᵍ)) ⋎ □(∼□(∼□(φᵍ))) by
    apply A!_replace this;
    . apply axiomK'!;
      apply nec!;
      apply contra!;
      exact Hilbert.goedelTranslated_axiomTc;
    . apply axiomK'!;
      apply nec!;
      apply contra!;
      apply axiomK'!;
      apply nec!;
      apply contra!;
      exact axiomT!
  apply Hilbert.S4Point2.Kripke.complete.complete;
  rintro F ⟨_, _⟩ V x;
  apply Formula.Kripke.Satisfies.or_def.mpr;
  by_contra hC;
  push_neg at hC;
  rcases hC with ⟨h₁, h₂⟩;

  replace h₁ := Formula.Kripke.Satisfies.dia_def.mp h₁;
  obtain ⟨y, Rxy, h₁⟩ := h₁;

  replace h₂ := Formula.Kripke.Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, h₂⟩ := h₂;

  obtain ⟨u, Ryu, Rzu⟩ := IsConfluent.confluent ⟨Rxy, Rxz⟩;

  have := Formula.Kripke.Satisfies.box_def.not.mp $ h₂ u Rzu;
  push_neg at this;
  obtain ⟨v, Ruv, h⟩ := this;

  have := h₁ v $ IsTrans.trans _ _ _ Ryu Ruv
  contradiction;

namespace Logic

open Formula.Kripke in
lemma mem_gAxiomPoint2_smallestMC_of_KC : (Axioms.Point2 (.atom 0)) ∈ Logic.KC.smallestMC := by
  have : □(∼□(.atom 0)) ⋎ □(∼□(∼□(.atom 0))) ∈ Logic.KC.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.WeakLEM (.atom 0);
    constructor;
    . simp;
    . simp [Axioms.WeakLEM, goedelTranslate]
      tauto;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply Hilbert.S4.Kripke.complete.complete;

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

lemma S4Point2.is_smallestMC_of_KC : Logic.S4Point2 = Logic.KC.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . exact Logic.sumNormal.subst $ mem_gAxiomPoint2_smallestMC_of_KC;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => apply Sublogic.subset h;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Hilbert.provable_goedelTranslated_of_provable Hilbert.KC Hilbert.S4Point2 ?_ (by trivial);
      rintro _ ⟨_, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩;
      . apply Sublogic.subset (L₁ := Logic.S4) (L₂ := Logic.S4Point2);
        apply modalCompanion_Int_S4.companion.mp;
        simp;
      . suffices Hilbert.S4Point2 ⊢! □(∼(s 0)ᵍ) ⋎ □(∼□(∼(s 0)ᵍ)) by simpa;
        exact Hilbert.S4Point2.goedelTranslated_axiomWLEM;

instance modalCompanion_KC_S4Point2 : ModalCompanion Logic.KC Logic.S4Point2 := by
  rw [Logic.S4Point2.is_smallestMC_of_KC];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.confluent)
    (MC := FrameClass.confluent_preorder)
    (by rw [Propositional.Logic.KC.Kripke.eq_confluent])
    (by rw [←Modal.Logic.S4Point2.is_smallestMC_of_KC, ←Modal.Logic.S4Point2.Kripke.confluent_preorder])
    (by rintro F hF; replace hF := Set.mem_setOf_eq.mp hF; apply Set.mem_setOf_eq.mpr; refine ⟨inferInstance, inferInstance⟩);

end Logic

end S4Point2


section GrzPoint2

lemma Logic.gGrzPoint2_of_KC : φ ∈ Logic.KC → φᵍ ∈ Logic.GrzPoint2 := by
  intro h;
  exact Sublogic.subset $ modalCompanion_KC_S4Point2.companion.mp h;

lemma Logic.GrzPoint2.is_largestMC_of_KC : Logic.GrzPoint2 = Logic.KC.largestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.subst (φ := □(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0)) ➝ (.atom 0)) (s := s);
        apply Logic.sumNormal.mem₂;
        simp;
      . apply Logic.sumNormal.subst (φ := ◇□(.atom 0) ➝ □◇(.atom 0)) (s := s);
        apply Logic.sumNormal.mem₁;
        rw [←Logic.S4Point2.is_smallestMC_of_KC]
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply Sublogic.subset (L₁ := Logic.S4Point2) (L₂ := Logic.GrzPoint2);
      rwa [Logic.S4Point2.is_smallestMC_of_KC]
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance modalCompanion_KC_GrzPoint2 : ModalCompanion Logic.KC Logic.GrzPoint2 := by
  rw [Logic.GrzPoint2.is_largestMC_of_KC];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_confluent)
    (MC := FrameClass.finite_confluent_partial_order)
    (by rw [Logic.KC.Kripke.eq_finite_confluent])
    (by rw [←Logic.GrzPoint2.is_largestMC_of_KC, Modal.Logic.GrzPoint2.Kripke.finite_confluent_partial_order])
    (by rintro F ⟨_, F_confl⟩; refine ⟨by tauto, inferInstance, inferInstance⟩)

end GrzPoint2


end LO.Modal
