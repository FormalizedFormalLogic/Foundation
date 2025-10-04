import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.ED
import Foundation.Modal.Neighborhood.Logic.ET4


namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsET5 (F : Frame) extends F.IsReflexive, F.IsEuclidean
protected abbrev FrameClass.ET5 : FrameClass := { F | F.IsET5 }

variable {F : Frame}

instance [F.IsReflexive] : F.NotContainsEmpty where
  not_contains_empty := by apply F.refl;

instance [F.IsReflexive] [F.IsEuclidean] : F.ContainsUnit where
  contains_unit := by
    ext x;
    suffices x ∈ F.box Set.univ by simpa;
    have H₁ : x ∈ (F.box $ F.dia Set.univ) → x ∈ (F.box $ Set.univ) := by simp [show F.dia Set.univ = Set.univ by ext; simp]
    apply H₁;
    apply F.eucl;
    simp;

instance : Frame.simple_blackhole.IsET5 where
  eucl := by
    intro X x hx;
    simp_all [Frame.simple_blackhole, Frame.box];

end Neighborhood


namespace ET5

instance : Sound Modal.ET5 FrameClass.ET5 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.ET5 := consistent_of_sound_frameclass FrameClass.ET5 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.ET5 FrameClass.ET5 := (minimalCanonicity Modal.ET5).completeness $ by sorry;

end ET5


instance : Modal.END4 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl | rfl);
    . apply Complete.complete (𝓜 := FrameClass.ET5)
      intro F hF;
      replace hF := Set.mem_setOf_eq.mp hF;
      apply valid_axiomN_of_ContainsUnit
    . sorry;
    . sorry;
  . sorry;

end LO.Modal
