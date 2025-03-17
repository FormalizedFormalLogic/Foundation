import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Logic.Sublogic.S4
import Foundation.Propositional.Kripke.Hilbert.LC

namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke


section S4Point3

lemma Hilbert.S4Point3.goedelTranslated_axiomDummett : Hilbert.S4Point3 ⊢! □(□ψᵍ ➝ χᵍ) ➝ □(ψᵍ ➝ χᵍ) := by
  apply axiomK'!;
  apply nec!;
  apply imp_swap'!;
  apply deduct'!;
  apply deduct!;
  have h₁ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ ➝ □ψᵍ := of'! $ Hilbert.goedelTranslated_axiomTc;
  have h₂ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ := by_axm!;
  have h₃ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! □ψᵍ ➝ χᵍ := by_axm!;
  exact h₃ ⨀ (h₁ ⨀ h₂);

private lemma Hilbert.S4Point.lemma₁ : Hilbert.S4 ⊢! □(□φ ➝ □ψ) ➝ □(□φ ➝ ψ) := by
  apply Hilbert.S4.Kripke.complete.complete;
  rintro F ⟨_, _⟩ V x h₁ y Rxy h₂;
  apply @h₁ y Rxy h₂;
  apply IsRefl.refl;

namespace Logic

lemma mem_gAxiomPoint3_smallestMC_of_LC : □(□(.atom 0) ➝ (.atom 1)) ⋎ □(□(.atom 1) ➝ (.atom 0)) ∈ Logic.LC.smallestMC := by
  have : □(□.atom 0 ➝ □.atom 1) ⋎ □(□.atom 1 ➝ □.atom 0) ∈ Logic.LC.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.Dummett (.atom 0) (.atom 1);
    simp [Axioms.Dummett, goedelTranslate];
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply or_replace!;
  repeat exact Hilbert.S4Point.lemma₁;

lemma S4Point3.is_smallestMC_of_LC : Logic.S4Point3 = Logic.LC.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . exact Logic.sumNormal.subst $ mem_gAxiomPoint3_smallestMC_of_LC;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => apply Logic.S4_ssubset_S4Point3.1 h;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Hilbert.provable_goedelTranslated_of_provable Hilbert.LC Hilbert.S4Point3 ?_ (by trivial);
      rintro _ ⟨_, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩;
      . apply Logic.S4_ssubset_S4Point3.1;
        apply modalCompanion_Int_S4.companion.mp;
        simp;
      . suffices Hilbert.S4Point3 ⊢! □(s 0ᵍ ➝ s 1ᵍ) ⋎ □(s 1ᵍ ➝ s 0ᵍ) by simpa [goedelTranslate];
        apply or_replace'! axiomPoint3!;
        repeat exact Hilbert.S4Point3.goedelTranslated_axiomDummett;

instance modalCompanion_LC_S4Point3 : ModalCompanion Logic.LC Logic.S4Point3 := by
  rw [Logic.S4Point3.is_smallestMC_of_LC];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.connected)
    (MC := Modal.Kripke.FrameClass.connected_preorder)
    (by rw [Propositional.Logic.LC.Kripke.eq_connected])
    (by rw [←Modal.Logic.S4Point3.is_smallestMC_of_LC, ←Modal.Logic.S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic])
    (by rintro F hF; replace hF := Set.mem_setOf_eq.mp hF; apply Set.mem_setOf_eq.mpr; refine ⟨inferInstance, inferInstance⟩);

end Logic

end S4Point3


section GrzPoint3

lemma Logic.gGrzPoint3_of_LC : φ ∈ Logic.LC → φᵍ ∈ Logic.GrzPoint3 := by
  intro h;
  exact S4Point3_ssubset_GrzPoint3.1 $ modalCompanion_LC_S4Point3.companion.mp h;

lemma Logic.GrzPoint3.is_largestMC_of_LC : Logic.GrzPoint3 = Logic.LC.largestMC := by
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
      . apply Logic.sumNormal.subst (φ := □(□(.atom 0) ➝ (.atom 1)) ⋎ □(□(.atom 1) ➝ (.atom 0))) (s := s);
        apply Logic.sumNormal.mem₁;
        rw [←Logic.S4Point3.is_smallestMC_of_LC]
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply S4Point3_ssubset_GrzPoint3.1;
      rwa [Logic.S4Point3.is_smallestMC_of_LC]
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance modalCompanion_LC_GrzPoint3 : ModalCompanion Logic.LC Logic.GrzPoint3 := by
  rw [Logic.GrzPoint3.is_largestMC_of_LC];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_connected)
    (MC := FrameClass.finite_connected_partial_order)
    (by rw [Logic.LC.Kripke.eq_finite_connected])
    (by rw [←Logic.GrzPoint3.is_largestMC_of_LC, Modal.Logic.GrzPoint3.eq_ReflexiveTransitiveAntiSymmetricConnectedFiniteKripkeFrameClass_Logic])
    (by rintro F ⟨_, F_confl⟩; refine ⟨by tauto, inferInstance, inferInstance⟩)

end GrzPoint3



end LO.Modal
