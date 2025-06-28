import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Logic.Extension
import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Hilbert.Glivenko
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (goedelTranslate)
open Modal
open Modal.Kripke

section S4

lemma Logic.gS4_of_Int : Logic.Int ⊢! φ → Logic.S4 ⊢! φᵍ := by
  apply provable_goedelTranslated_of_provable Hilbert.Int Logic.S4;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

lemma Logic.S4.is_smallestMC_of_Int : Logic.S4 = Logic.Int.smallestMC := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Modal.Hilbert.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩) <;>
      . apply Logic.sumNormal.mem₁!; simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => tauto;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Modal.Logic.subst! _ ih;
    | nec ih => apply Entailment.nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; apply Logic.gS4_of_Int hφ;

instance : Sound Logic.Int.smallestMC FrameClass.S4 := by
  rw [←Logic.S4.is_smallestMC_of_Int];
  infer_instance;

instance modalCompanion_Int_S4 : ModalCompanion Logic.Int Logic.S4 := by
  rw [Logic.S4.is_smallestMC_of_Int];
  apply Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.all
    FrameClass.S4
    (by intro F _; constructor);

end S4



section Grz

lemma Logic.gGrz_of_Int : Logic.Int ⊢! φ → Logic.Grz ⊢! φᵍ := λ h ↦ WeakerThan.pbl $ gS4_of_Int h

lemma Logic.Grz.is_largestMC_of_Int : Logic.Grz = Logic.Int.largestMC := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Modal.Hilbert.rec! with
    | maxm h => rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl $ Logic.S4.is_smallestMC_of_Int ▸ h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : Sound Logic.Int.largestMC FrameClass.finite_Grz := by
  rw [←Logic.Grz.is_largestMC_of_Int];
  infer_instance;

instance modalCompanion_Int_Grz : ModalCompanion Logic.Int Logic.Grz := by
  rw [Logic.Grz.is_largestMC_of_Int];
  apply Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_all
    FrameClass.finite_Grz
    $ by rintro F hF; simp_all only [Set.mem_setOf_eq]; exact {}

end Grz


section glivenko

lemma Logic.iff_provable_Cl_provable_dia_gS4 : Logic.Cl ⊢! φ ↔ Logic.S4 ⊢! ◇φᵍ := by
  constructor;
  . intro h;
    suffices Logic.S4 ⊢! □◇φᵍ by exact axiomT'! this;
    have := modalCompanion_Int_S4.companion.mp $ Hilbert.glivenko.mpr h;
    rwa [Logic.S4.Kripke.preorder] at this ⊢;
  . intro h;
    apply Hilbert.glivenko.mp;
    apply modalCompanion_Int_S4.companion.mpr;
    have : Logic.S4 ⊢! □◇φᵍ := nec! h;
    rwa [Logic.S4.Kripke.preorder] at this ⊢;

end glivenko


section boxdot

/--
  Chagrov & Zakharyaschev 1997, Theorem 3.89
-/
theorem embedding_Int_GL {φ : Propositional.Formula ℕ} : Logic.Int ⊢! φ ↔ Logic.GL ⊢! φᵍᵇ:= by
  exact Iff.trans modalCompanion_Int_Grz.companion Logic.iff_provable_boxdot_GL_provable_Grz.symm

end boxdot


end LO.Modal
