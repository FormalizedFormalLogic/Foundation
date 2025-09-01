import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Logic.Extension
import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Hilbert.Glivenko
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke

section S4

lemma Logic.gS4_of_Int : Hilbert.Int ⊢! φ → Hilbert.S4 ⊢! φᵍ := by
  apply provable_goedelTranslated_of_provable Hilbert.Int Hilbert.S4;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

lemma Modal.S4.is_smallestMC_of_Int : Modal.S4 = (smallestMC 𝗜𝐧𝐭) := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    simp only [Hilbert.Normal.iff_logic_provable_provable] at hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl) <;>
      . apply Logic.sumNormal.mem₁!;
        simp;
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
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      simp only [theory, Propositional.Logic.iff_provable, Set.mem_setOf_eq] at hφ;
      simpa using Logic.gS4_of_Int hφ;

instance : Sound (smallestMC 𝗜𝐧𝐭) FrameClass.S4 := by
  rw [←Modal.S4.is_smallestMC_of_Int];
  infer_instance;

instance modalCompanion_Int_S4 : ModalCompanion 𝗜𝐧𝐭 Modal.S4 := by
  rw [Modal.S4.is_smallestMC_of_Int];
  apply Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.all
    FrameClass.S4;
  intro F _;
  constructor;

end S4



section Grz

lemma Logic.gGrz_of_Int : Hilbert.Int ⊢! φ → Hilbert.Grz ⊢! φᵍ := λ h ↦ WeakerThan.pbl $ gS4_of_Int h

lemma Logic.Grz.is_largestMC_of_Int : Modal.Grz = (Logic.largestMC 𝗜𝐧𝐭) := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    simp only [Hilbert.Normal.iff_logic_provable_provable] at hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h => rcases h with (rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl $ Modal.S4.is_smallestMC_of_Int ▸ h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : Sound (Logic.largestMC 𝗜𝐧𝐭) FrameClass.finite_Grz := by
  rw [←Logic.Grz.is_largestMC_of_Int];
  infer_instance;

instance modalCompanion_Int_Grz : ModalCompanion 𝗜𝐧𝐭 Modal.Grz := by
  rw [Logic.Grz.is_largestMC_of_Int];
  apply Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_all
    FrameClass.finite_Grz
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {}

end Grz


section glivenko

lemma Logic.iff_provable_Cl_provable_dia_gS4 : 𝐂𝐥 ⊢! φ ↔ Hilbert.S4 ⊢! ◇φᵍ := by
  constructor;
  . intro h;
    suffices Hilbert.S4 ⊢! □◇φᵍ by exact axiomT'! this;
    have := modalCompanion_Int_S4.companion.mp $ iff_negneg_Int_Cl.mpr h;
    simp only [goedelTranslate, Hilbert.Normal.iff_logic_provable_provable] at this;
    cl_prover [this];
  . intro h;
    replace h : Hilbert.S4 ⊢! □◇φᵍ := nec! h;
    apply iff_negneg_Int_Cl.mp;
    apply modalCompanion_Int_S4.companion.mpr;
    simp only [Hilbert.Normal.iff_logic_provable_provable];
    cl_prover [h];

end glivenko


section boxdot

/--
  Chagrov & Zakharyaschev 1997, Theorem 3.89
-/
theorem embedding_Int_GL {φ : Propositional.Formula ℕ} : 𝗜𝐧𝐭 ⊢! φ ↔ Modal.GL ⊢! φᵍᵇ:= by
  exact Iff.trans modalCompanion_Int_Grz.companion iff_boxdot_GL_Grz.symm

end boxdot


end LO.Modal
