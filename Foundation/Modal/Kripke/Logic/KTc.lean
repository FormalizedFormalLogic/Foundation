import Foundation.Modal.Kripke.Logic.KB4


namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsKTc := Frame.IsCoreflexive

protected abbrev FrameClass.KTc : FrameClass := { F | F.IsKTc }

instance [F.IsKTc] : F.IsKB4 where

end Kripke




namespace Logic.KTc.Kripke

instance : Sound (Hilbert.KTc) Kripke.FrameClass.KTc := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_corefl _ rfl;
  exact Kripke.validate_AxiomTc_of_coreflexive (corefl := F_corefl);

instance : Entailment.Consistent (Hilbert.KTc) := consistent_of_sound_frameclass Kripke.FrameClass.KTc $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical (Hilbert.KTc) Kripke.FrameClass.KTc := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete (Hilbert.KTc) Kripke.FrameClass.KTc := inferInstance

lemma corefl : Logic.KTc = Kripke.FrameClass.KTc.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.KB4 ⪱ Logic.KTc := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.KB4 ⊧ φ → FrameClass.KTc ⊧ φ by
      simpa [KB4.Kripke.refl_trans, KTc.Kripke.corefl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KTc ⊢! φ ∧ ¬FrameClass.KB4 ⊧ φ by simpa [KB4.Kripke.refl_trans];
    use (Axioms.Tc (.atom 0));
    constructor;
    . exact axiomTc!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . exact {
          symm := by simp [M],
          trans := by simp [M],
        }
      . suffices ∃ x, (x : M.World) ≠ 0 by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        use 1;
        aesop;

end Logic.KTc.Kripke

end LO.Modal
