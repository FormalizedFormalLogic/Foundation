import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.eucl : FrameClass := { F | Euclidean F }
-- abbrev Kripke.EuclideanFiniteFrameClass : FiniteFrameClass := { F | Euclidean F.Rel }

namespace Hilbert.K5.Kripke

instance sound : Sound (Hilbert.K5) Kripke.FrameClass.eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;
  . unfold Kripke.FrameClass.eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.euclidean_def];

instance consistent : Entailment.Consistent (Hilbert.K5) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance canonical : Canonical (Hilbert.K5) Kripke.FrameClass.eucl := ⟨Canonical.euclidean⟩

instance complete : Complete (Hilbert.K5) Kripke.FrameClass.eucl := inferInstance

end Hilbert.K5.Kripke

end LO.Modal
