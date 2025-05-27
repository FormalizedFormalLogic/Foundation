import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Logic.Extension
import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Hilbert.Glivenko
import Foundation.Propositional.Logic.WellKnown

namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Modal
open Modal.Kripke

section S4

lemma Logic.gS4_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.S4 := by
  apply Hilbert.provable_goedelTranslated_of_provable Hilbert.Int Hilbert.S4;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

lemma Logic.S4.is_smallestMC_of_Int : Logic.S4 = Logic.Int.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => tauto;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Logic.gS4_of_Int hφ;

instance modalCompanion_Int_S4 : ModalCompanion Logic.Int Logic.S4 := by
  rw [Logic.S4.is_smallestMC_of_Int];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.all)
    (MC := Modal.Kripke.FrameClass.preorder)
    (by rw [Logic.Int.Kripke.eq_all])
    (by rw [←Logic.S4.is_smallestMC_of_Int, ←Modal.Logic.S4.Kripke.preorder])
    (by simp; intro F; infer_instance;);

end S4



section Grz

lemma Logic.gGrz_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.Grz := by
  intro h;
  apply Sublogic.subset $ Logic.gS4_of_Int h;

lemma Logic.Grz.is_largestMC_of_Int : Logic.Grz = Logic.Int.largestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.subst (φ := □(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0)) ➝ (.atom 0)) (s := s);
        apply Logic.sumNormal.mem₂;
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply Sublogic.subset (L₁ := Logic.S4) (L₂ := Logic.Grz);
      rwa [Logic.S4.is_smallestMC_of_Int]
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance modalCompanion_Int_Grz : ModalCompanion Logic.Int Logic.Grz := by
  rw [Logic.Grz.is_largestMC_of_Int];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_all)
    (MC := FrameClass.finite_partial_order)
    (by rw [Logic.Int.Kripke.eq_all_finite])
    (by rw [←Logic.Grz.is_largestMC_of_Int, Modal.Logic.Grz.Kripke.finite_partial_order])
    (by rintro F ⟨⟩; refine ⟨by tauto, inferInstance⟩);

end Grz


section glivenko

lemma Logic.iff_provable_Cl_provable_dia_gS4 : (φ ∈ Logic.Cl) ↔ (◇φᵍ ∈ (Logic.S4)) := by
  constructor;
  . intro h;
    suffices □◇φᵍ ∈ Logic.S4 by exact axiomT'! this;
    have := modalCompanion_Int_S4.companion.mp $ Hilbert.glivenko.mpr h;
    rw [Logic.S4.Kripke.preorder] at this ⊢;
    exact this;
  . intro h;
    apply Hilbert.glivenko.mp;
    apply modalCompanion_Int_S4.companion.mpr;
    have : □◇φᵍ ∈ Logic.S4 := nec! h;
    rw [Logic.S4.Kripke.preorder] at this ⊢;
    exact this;

end glivenko


section boxdot

/--
  Chagrov & Zakharyaschev 1997, Theorem 3.89
-/
theorem embedding_Int_GL {φ : Propositional.Formula ℕ} : φ ∈ Logic.Int ↔ φᵍᵇ ∈ Logic.GL := by
  exact Iff.trans modalCompanion_Int_Grz.companion Logic.iff_provable_boxdot_GL_provable_Grz.symm

end boxdot


end LO.Modal
