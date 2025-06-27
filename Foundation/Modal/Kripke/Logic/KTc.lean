import Foundation.Modal.Kripke.Logic.KB4


namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsKTc := Frame.IsCoreflexive

protected abbrev FrameClass.KTc : FrameClass := { F | F.IsKTc }

instance [F.IsKTc] : F.IsKB4 where

end Kripke




namespace Logic.KTc.Kripke

instance sound : Sound (Logic.KTc) Kripke.FrameClass.KTc := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_corefl _ rfl;
  exact Kripke.validate_AxiomTc_of_coreflexive (corefl := F_corefl);

instance consistent : Entailment.Consistent (Logic.KTc) := consistent_of_sound_frameclass Kripke.FrameClass.KTc $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Logic.KTc) Kripke.FrameClass.KTc := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Logic.KTc) Kripke.FrameClass.KTc := inferInstance

end Logic.KTc.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KTc.Kripke.corefl : Logic.KTc = Kripke.FrameClass.KTc.logic := eq_hilbert_logic_frameClass_logic

@[simp]
instance : Logic.KB4 ⪱ Logic.KTc := by
  constructor;
  . rw [KB4.Kripke.refl_trans, KTc.Kripke.corefl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . suffices ∃ φ, Hilbert.KTc ⊢! φ ∧ ¬FrameClass.IsKB4 ⊧ φ by
      rw [KB4.Kripke.refl_trans];
      tauto;
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

end Logic

end LO.Modal
