import Foundation.Modal.Kripke.Preservation
import Foundation.Modal.Kripke.Hilbert.KT4B

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F ∧ Euclidean F }

namespace Hilbert.S5

instance Kripke.sound : Sound (Hilbert.S5) (Kripke.ReflexiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;
  . unfold ReflexiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.S5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.S5) (ReflexiveEuclideanFrameClass) := ⟨⟨Canonical.reflexive, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.S5) (ReflexiveEuclideanFrameClass) := inferInstance

end Hilbert.S5


namespace Kripke

abbrev UniversalFrameClass : FrameClass := { F | Universal F }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : UniversalFrameClass ⊧ φ ↔ ReflexiveEuclideanFrameClass ⊧ φ := by
  constructor;
  . intro h F hF V r;
    let M : Model := ⟨F, V⟩;
    apply Model.PointGenerated.modal_equivalent_at_root  (M := ⟨F, V⟩) (by apply trans_of_refl_eucl hF.1 hF.2) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) (M↾r).Val;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

end Kripke


namespace Hilbert.S5

instance Kripke.soundUniversal : Sound (Hilbert.S5) (Kripke.UniversalFrameClass) := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact Kripke.sound.sound hF;
⟩

instance Kripke.completeUniversal : Complete (Hilbert.S5) (Kripke.UniversalFrameClass) := ⟨by
  intro φ hF;
  apply Kripke.complete.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

end Hilbert.S5


abbrev Kripke.ReflexiveEuclideanFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }

lemma Kripke.eq_ReflexiveTransitiveSymmetricFiniteFrameClass_ReflexiveEuclideanFiniteFrameClass : ReflexiveTransitiveSymmetricFiniteFrameClass = ReflexiveEuclideanFiniteFrameClass := by
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

end LO.Modal
