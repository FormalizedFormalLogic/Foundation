import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KTc

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.refl_corefl : FrameClass := { F | IsRefl _ F ∧ IsCoreflexive _ F }
protected abbrev Kripke.FrameClass.equality : FrameClass := { F | IsEquality _ F }

lemma Kripke.FrameClass.eq_equality_refl_corefl : Kripke.FrameClass.equality = Kripke.FrameClass.refl_corefl := by
  ext F;
  constructor;
  . intro F_eq;
    replace F_eq := Set.mem_setOf_eq.mp F_eq;
    constructor <;> infer_instance;
  . rintro ⟨hRefl, hCorefl⟩;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

namespace Hilbert.Triv.Kripke

instance sound_refl_corefl : Sound (Hilbert.Triv) Kripke.FrameClass.refl_corefl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F ⟨_, _⟩ _ (rfl | rfl);
    . exact validate_AxiomT_of_reflexive;
    . exact validate_AxiomTc_of_coreflexive;

instance sound_equality : Sound (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  infer_instance;

instance consistent : Entailment.Consistent (Hilbert.Triv) := consistent_of_sound_frameclass Kripke.FrameClass.refl_corefl $ by
  use whitepoint;
  constructor <;> infer_instance;

instance cannonical_refl_corefl : Canonical (Hilbert.Triv) Kripke.FrameClass.refl_corefl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete_refl_corefl : Complete (Hilbert.Triv) Kripke.FrameClass.refl_corefl := inferInstance

instance complete_equality : Complete (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  infer_instance;

end Hilbert.Triv.Kripke


end LO.Modal
