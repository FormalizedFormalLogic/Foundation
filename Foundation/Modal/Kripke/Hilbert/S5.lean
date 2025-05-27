import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Hilbert.KT4B

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

protected abbrev FrameClass.refl_eucl : FrameClass := { F | IsRefl _ F ∧ IsEuclidean _ F }

protected abbrev FrameClass.universal : FrameClass := { F | IsUniversal _ F }

protected abbrev FrameClass.finite_refl_eucl: FrameClass := { F | F.IsFinite ∧ IsRefl _ F ∧ IsEuclidean _ F }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ Kripke.FrameClass.refl_eucl ⊧ φ := by
  constructor;
  . rintro h F ⟨F_refl, F_eucl⟩ V r;
    apply @Model.pointGenerate.modal_equivalent_at_root _ _ |>.mp;
    apply h;
    apply Set.mem_setOf_eq.mpr;
    exact Frame.pointGenerate.isUniversal (r := r) (refl := F_refl) (eucl := F_eucl);
  . rintro h F F_univ;
    replace F_univ := Set.mem_setOf_eq.mp F_univ
    apply h;
    constructor <;> infer_instance;

end Kripke


namespace Hilbert.S5.Kripke

instance sound_refl_eucl : Sound (Hilbert.S5) Kripke.FrameClass.refl_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFive_of_euclidean;

instance sound_universal : Sound (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact sound_refl_eucl.sound hF;
⟩

instance consistent : Entailment.Consistent (Hilbert.S5) := consistent_of_sound_frameclass Kripke.FrameClass.refl_eucl $ by
  use whitepoint;
  refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S5) Kripke.FrameClass.refl_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete_refl_eucl : Complete (Hilbert.S5) Kripke.FrameClass.refl_eucl := inferInstance

instance complete_universal : Complete (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply Kripke.complete_refl_eucl.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

end Hilbert.S5.Kripke

lemma Logic.S5.Kripke.refl_eucl : Logic.S5 = FrameClass.refl_eucl.logic := eq_hilbert_logic_frameClass_logic
lemma Logic.S5.Kripke.universal : Logic.S5 = FrameClass.universal.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal
