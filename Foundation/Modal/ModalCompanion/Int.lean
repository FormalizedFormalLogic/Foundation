import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Logic.SumNormal
import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Hilbert.Glivenko
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke

lemma Kripke.sound_frameClass_of_equiv (L₁ L₂ : Logic ℕ) [L₁ ≊ L₂] {C : Kripke.FrameClass} [Sound L₁ C] : Sound L₂ C := by grind;
lemma Kripke.complete_frameClass_of_equiv (L₁ L₂ : Logic ℕ) [L₁ ≊ L₂] {C : Kripke.FrameClass} [Complete L₁ C] : Complete L₂ C := by grind;


lemma gS4_of_Int : Propositional.Int ⊢ φ → Modal.S4 ⊢ φᵍ := by
  apply provable_gödelTranslated_of_provable;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

namespace S4

instance : Modal.S4 ≊ Propositional.Int.smallestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h => rcases h with (rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | subst ih => apply Logic.subst _ ih;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ih => apply nec! ih;
    | mem₁ h => tauto;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply gS4_of_Int;
      simpa [theory, Propositional.Logic.iff_provable, Set.mem_setOf_eq] using hφ;

lemma eq_smallestMC_of_Int : Modal.S4 = Propositional.Int.smallestMC := Logic.eq_of_equiv

instance : Sound Propositional.Int.smallestMC FrameClass.S4 := Kripke.sound_frameClass_of_equiv Modal.S4 Propositional.Int.smallestMC

instance : ModalCompanion Propositional.Int Modal.S4 := by
  apply eq_smallestMC_of_Int ▸
    Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.all
    FrameClass.S4;
  intro F _;
  constructor;

end S4




instance : Propositional.Int.smallestMC ⪯ Modal.Grz := calc
  _ ≊ Modal.S4  := by symm; infer_instance;
  _ ⪯ Modal.Grz := inferInstance


namespace Grz

instance : Modal.Grz ≊ Propositional.Int.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h => rcases h with (rfl | rfl) <;> simp;
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

lemma is_largestMC_of_Int : Modal.Grz = Propositional.Int.largestMC := Logic.eq_of_equiv

instance : Sound Propositional.Int.largestMC FrameClass.finite_Grz := Kripke.sound_frameClass_of_equiv Modal.Grz Propositional.Int.largestMC

instance : ModalCompanion Propositional.Int Modal.Grz := by
  apply is_largestMC_of_Int ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_all
    FrameClass.finite_Grz
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {}

end Grz


lemma iff_provable_Cl_provable_dia_gS4 : Propositional.Cl ⊢ φ ↔ Modal.S4 ⊢ ◇φᵍ := by
  constructor;
  . intro h;
    suffices Modal.S4 ⊢ □◇φᵍ by exact axiomT'! this;
    have : Modal.S4 ⊢ (∼∼φ)ᵍ := ModalCompanion.companion.mp $ glivenko.mpr h;
    cl_prover [this];
  . intro h;
    apply glivenko.mp;
    suffices Modal.S4 ⊢ (∼∼φ)ᵍ by exact ModalCompanion.companion.mpr this;
    replace h : Modal.S4 ⊢ □◇φᵍ := nec! h;
    cl_prover [h];

/--
  Chagrov & Zakharyaschev 1997, Theorem 3.89
-/
theorem embedding_Int_GL : Propositional.Int ⊢ φ ↔ Modal.GL ⊢ φᵍᵇ:= Iff.trans ModalCompanion.companion iff_boxdot_GL_Grz.symm


end LO.Modal
