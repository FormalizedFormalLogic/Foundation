import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KB4

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent

protected abbrev Kripke.FrameClass.corefl : FrameClass := { F | IsCoreflexive _ F.Rel }

namespace Hilbert.KTc.Kripke

instance sound : Sound (Hilbert.KTc) Kripke.FrameClass.corefl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_corefl _ rfl;
  exact Kripke.validate_AxiomTc_of_coreflexive (corefl := F_corefl);

instance consistent : Entailment.Consistent (Hilbert.KTc) := consistent_of_sound_frameclass Kripke.FrameClass.corefl $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.KTc) FrameClass.corefl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KTc) FrameClass.corefl := inferInstance

end Hilbert.KTc.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KTc.Kripke.corefl : Logic.KTc = FrameClass.corefl.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.KB4 Logic.KTc := ⟨by
  constructor;
  . rw [KB4.Kripke.refl_trans, KTc.Kripke.corefl];
    rintro φ hφ F F_corefl;
    replace hF := Set.mem_setOf_eq.mp F_corefl;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.KTc ⊢! φ ∧ ¬Kripke.FrameClass.symm_trans ⊧ φ by
      rw [KB4.Kripke.refl_trans];
      tauto;
    use (Axioms.Tc (.atom 0));
    constructor;
    . exact axiomTc!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by simp [M]⟩, ⟨by simp [M]⟩⟩
      . suffices ∃ x, (x : M.World) ≠ 0 by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        use 1;
        aesop;
⟩
end Logic

end LO.Modal
