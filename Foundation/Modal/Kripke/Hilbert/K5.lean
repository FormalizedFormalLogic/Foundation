import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.FiniteFrame

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }
abbrev Kripke.EuclideanFiniteFrameClass : FiniteFrameClass := { F | Euclidean F.Rel }

namespace Hilbert.K5

instance Kripke.sound : Sound (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;
  . unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];

instance Kripke.consistent : System.Consistent (Hilbert.K5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];

end Hilbert.K5

end LO.Modal
