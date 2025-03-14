import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Hilbert.KT4B

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

protected abbrev FrameClass.refl_eucl : FrameClass := { F | Reflexive F ∧ Euclidean F }

namespace FrameClass.refl_eucl

lemma isMultiGeachean : FrameClass.refl_eucl = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.euclidean_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.refl_eucl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertS5 : Kripke.FrameClass.refl_eucl.Validates Hilbert.S5.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive $ by assumption
  . exact validate_AxiomFive_of_euclidean $ by assumption

end FrameClass.refl_eucl


protected abbrev FrameClass.universal : FrameClass := { F | Universal F }

protected abbrev FrameClass.finite_refl_eucl: FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Euclidean F.Rel }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ Kripke.FrameClass.refl_eucl ⊧ φ := by
  constructor;
  . rintro h F ⟨F_refl, F_eucl⟩ V r;
    apply @Model.pointGenerate.modal_equivalent_at_root _ _ |>.mp;
    apply h;
    exact Frame.pointGenerate.rel_universal_of_refl_eucl F_refl F_eucl;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

lemma eq_finite_symm_preorder_finite_refl_eucl : Kripke.FrameClass.finite_symm_preorder = FrameClass.finite_refl_eucl := by
  ext F;
  constructor;
  . rintro ⟨_, hRefl, hTrans, hSymm⟩;
    refine ⟨inferInstance, ?_, ?_⟩;
    . assumption;
    . exact eucl_of_symm_trans hSymm hTrans;
  . rintro ⟨_, hRefl, hEucl⟩;
    refine ⟨inferInstance, hRefl, ?_, ?_⟩;
    . exact trans_of_refl_eucl hRefl hEucl;
    . exact symm_of_refl_eucl hRefl hEucl;

end Kripke


namespace Hilbert.S5.Kripke

instance sound_refl_eucl : Sound (Hilbert.S5) Kripke.FrameClass.refl_eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.refl_eucl.validates_HilbertS5

instance sound_universal : Sound (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact sound_refl_eucl.sound hF;
⟩

instance consistent : Entailment.Consistent (Hilbert.S5) :=
  consistent_of_sound_frameclass Kripke.FrameClass.refl_eucl (by simp)

instance canonical : Canonical (Hilbert.S5) Kripke.FrameClass.refl_eucl := ⟨⟨Canonical.reflexive, Canonical.euclidean⟩⟩

instance complete : Complete (Hilbert.S5) Kripke.FrameClass.refl_eucl := inferInstance

instance complete_universal : Complete (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply Kripke.complete.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

end Hilbert.S5.Kripke

end LO.Modal
