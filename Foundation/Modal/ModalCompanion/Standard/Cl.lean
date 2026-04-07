module

public import Foundation.Logic.Embedding
public import Foundation.Modal.Boxdot.GL_Grz
public import Foundation.Modal.Kripke.Logic.S5
public import Foundation.Modal.Kripke.Logic.S5Grz
public import Foundation.Modal.ModalCompanion.Standard.Basic
public import Foundation.Modal.Boxdot.Ver_Triv
public import Foundation.Propositional.Kripke.Hilbert.Cl

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke


namespace S5

@[simp, grind .]
lemma gödelTranslated_axiomLEM : Modal.S5 ⊢ (Axioms.LEM φ)ᵍ := by
  apply Complete.complete (𝓜 := FrameClass.S5);
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Modal.Formula.Kripke.Satisfies.or_def.mpr;
  apply or_iff_not_imp_left.mpr;
  intro h y Rxy hφ;
  apply h;
  apply Modal.gödelTranslated_persistency hφ;
  apply F.symm Rxy;

end S5


namespace Propositional.Cl

lemma provable_S5_of_mem : φ ∈ Propositional.Cl → Modal.S5 ⊢ φᵍ := by
  apply Propositional.Hilbert.provable_gödelTranslated_of_mem_logic;
  rintro _ ⟨a, (⟨_, rfl⟩ | ⟨_, _, rfl⟩), rfl⟩ <;> simp;

theorem modalCompanion_S5 : ModalCompanion Propositional.Cl Modal.S5 := by
  apply modalCompanion_via_kripkeSemantics (P := λ F => IsRightEuclidean F);
  . apply provable_S5_of_mem;
  . intro φ;
    apply Hilbert.Cl.instKripkeComplete.complete;
  . rintro φ hφ F _ _;
    apply Modal.instSoundLogicNatFormulaFrameClassS5S5.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

lemma provable_S5Grz_of_mem : φ ∈ Propositional.Cl → Modal.S5Grz ⊢ φᵍ := fun h ↦ WeakerThan.pbl $ provable_S5_of_mem h

theorem modalCompanion_S5Grz : ModalCompanion Propositional.Cl Modal.S5Grz := by
  apply modalCompanion_via_kripkeSemantics (P := λ {κ} F => Finite κ ∧ Std.Symm F);
  . apply provable_S5Grz_of_mem;
  . intro φ;
    apply Hilbert.Cl.instKripkeCompleteFinite.complete;
  . rintro φ hφ F _ ⟨_, _⟩;
    apply Logic.instSoundNatFormulaFrameClassS5GrzFinite_Triv.sound;
    . grind;
    . apply Set.mem_setOf_eq.mpr;
      exact {};

theorem modalCompanion_Triv : ModalCompanion Propositional.Cl Modal.Triv := by
  intro φ;
  apply Iff.trans modalCompanion_S5Grz;
  apply Entailment.Equiv.iff.mp;
  infer_instance;

theorem boxdotModalCompanion_Ver : ∀ φ, φ ∈ Propositional.Cl ↔ Modal.Ver ⊢ φᵍᵇ :=
  λ _ => Iff.trans modalCompanion_Triv $ Modal.Logic.iff_boxdotTranslated_Ver_Triv.symm

/-
instance : Entailment.FaithfullyEmbeddable Propositional.Cl Modal.Ver where
  prop := ⟨(·ᵍᵇ), fun _ ↦ embedding_Cl_Ver.symm⟩
-/

end Propositional.Cl

end LO

end
