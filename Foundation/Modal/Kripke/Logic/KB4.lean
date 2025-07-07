import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K45
import Foundation.Modal.Kripke.Logic.KB

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsKB4 (F : Kripke.Frame) extends F.IsSymmetric, F.IsTransitive

protected abbrev FrameClass.IsKB4 : FrameClass := { F | F.IsKB4 }

instance [F.IsKB4] : F.IsK45 where

end Kripke


namespace Logic.KB4.Kripke

instance sound : Sound Logic.KB4 FrameClass.IsKB4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent Logic.KB4 := consistent_of_sound_frameclass FrameClass.IsKB4 $ by
  use whitepoint;
  constructor;

instance canonical : Canonical Logic.KB4 FrameClass.IsKB4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor
⟩

instance complete : Complete Logic.KB4 FrameClass.IsKB4 := inferInstance

end Logic.KB4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KB4.Kripke.refl_trans : Logic.KB4 = FrameClass.IsKB4.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K45 ⪱ Logic.KB4 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.IsK45 ⊧ φ → FrameClass.IsKB4 ⊧ φ by
      simpa [K45.Kripke.trans_eucl, KB4.Kripke.refl_trans];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KB4 ⊢! φ ∧ ¬FrameClass.IsK45 ⊧ φ by simpa [K45.Kripke.trans_eucl];
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . simp only [Fin.isValue, Set.mem_setOf_eq];
        refine { trans := by omega, reucl := by tauto };
      . simp [Semantics.Realize, Satisfies];

instance : Logic.KB ⪱ Logic.KB4 := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KB4 ⊢! φ ∧ ¬FrameClass.KB ⊧ φ by simpa [KB.Kripke.symm];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . simp only [bne_iff_ne, ne_eq, Set.mem_setOf_eq];
        refine { symm := by tauto };
      . simp [Semantics.Realize, Satisfies];
        tauto;

end Logic

end LO.Modal
