module

public import Foundation.Logic.Embedding
public import Foundation.Modal.Boxdot.GL_Grz
public import Foundation.Modal.ModalCompanion.Standard.Basic
public import Foundation.Propositional.Kripke.Hilbert.Int.Basic
public import Foundation.Propositional.Hilbert.Minimal.Glivenko

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke

namespace Propositional.Int

lemma provable_S4_of_mem : φ ∈ Propositional.Int → Modal.S4 ⊢ φᵍ := by
  apply Propositional.Hilbert.provable_gödelTranslated_of_mem_logic;
  rintro _ ⟨φ, ⟨_, rfl⟩, rfl⟩;
  simp;

theorem modalCompanion_S4 : ModalCompanion Propositional.Int Modal.S4 := by
  apply modalCompanion_via_kripkeSemantics (P := λ _ => True);
  . apply provable_S4_of_mem;
  . intro φ;
    apply Hilbert.Int.instKripkeComplete.complete;
  . rintro φ hφ F _ _;
    apply Modal.S4.instSoundLogicNatFormulaFrameClassS4.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

lemma provable_Grz_of_mem : φ ∈ Propositional.Int → Modal.Grz ⊢ φᵍ := fun h ↦ WeakerThan.pbl $ provable_S4_of_mem h

theorem modalCompanion_Grz : ModalCompanion Propositional.Int Modal.Grz := by
  apply modalCompanion_via_kripkeSemantics (P := λ {κ} _ => Finite κ);
  . apply provable_Grz_of_mem;
  . intro φ;
    apply Hilbert.Int.instKripkeCompleteFinite.complete;
  . rintro φ hφ F _ _;
    apply Modal.instSoundLogicNatFormulaFrameClassGrzFinite_Grz.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

theorem boxdotModalCompanion_GL : ∀ φ, φ ∈ Propositional.Int ↔ Modal.GL ⊢ φᵍᵇ :=
  λ _ => Iff.trans modalCompanion_Grz $ Modal.iff_provable_boxdot_GL_provable_Grz.symm

/-
instance : Entailment.FaithfullyEmbeddable Propositional.Int Modal.GL where
  prop := ⟨(·ᵍᵇ), fun _ ↦ embedding_Int_GL.symm⟩
-/

end Propositional.Int


namespace Propositional.Cl

lemma iff_mem_S4_dia : φ ∈ Propositional.Cl ↔ Modal.S4 ⊢ ◇φᵍ := by
  constructor;
  . intro h;
    exact unnec! $ Propositional.Int.modalCompanion_S4.mp $ Hilbert.glivenko.mpr h;
  . intro h;
    exact Hilbert.glivenko.mp $ Propositional.Int.modalCompanion_S4.mpr $ nec! h;

end Propositional.Cl

end LO

end
