import Foundation.Modal.Kripke.Preservation
import Foundation.Modal.Kripke.Hilbert.KT4B

namespace LO.Modal

open Kripke
open Geachean

namespace Kripke

protected abbrev FrameClass.refl_eucl : FrameClass := { F | Reflexive F ∧ Euclidean F }

protected abbrev FrameClass.universal : FrameClass := { F | Universal F }

protected abbrev FiniteFrameClass.refl_eucl : FiniteFrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ Kripke.FrameClass.refl_eucl ⊧ φ := by
  constructor;
  . intro h F hF V r;
    let M : Model := ⟨F, V⟩;
    apply Model.PointGenerated.modal_equivalent_at_root  (M := ⟨F, V⟩) (by apply trans_of_refl_eucl hF.1 hF.2) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) (M↾r).Val;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

lemma eq_ReflexiveTransitiveSymmetricFiniteFrameClass_ReflexiveEuclideanFiniteFrameClass : Kripke.FiniteFrameClass.symm_preorder = FiniteFrameClass.refl_eucl := by
  ext F;
  constructor;
  . rintro ⟨hRefl, hTrans, hSymm⟩;
    constructor;
    . assumption;
    . exact eucl_of_symm_trans hSymm hTrans;
  . rintro ⟨hRefl, hEucl⟩;
    refine ⟨hRefl, ?_, ?_⟩;
    . exact trans_of_refl_eucl hRefl hEucl;
    . exact symm_of_refl_eucl hRefl hEucl;

end Kripke

namespace Hilbert.S5.Kripke

instance sound_refl_eucl : Sound (Hilbert.S5) Kripke.FrameClass.refl_eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;
  . unfold Kripke.FrameClass.refl_eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];

instance sound_universal : Sound (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact sound_refl_eucl.sound hF;
⟩

instance consistent : Entailment.Consistent (Hilbert.S5) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

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
