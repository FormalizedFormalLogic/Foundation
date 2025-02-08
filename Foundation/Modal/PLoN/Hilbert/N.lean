import Foundation.Modal.PLoN.Hilbert.Soundness
import Foundation.Modal.PLoN.Completeness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open PLoN

namespace PLoN

abbrev AllFrameClass : PLoN.FrameClass := Set.univ

instance : AllFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ _ => True⟩;
  tauto;

end PLoN

namespace Hilbert.N

instance : AllFrameClass.DefinedBy Hilbert.N.axiomInstances := ⟨by simp_all [Hilbert.axiomInstances]⟩

instance : System.Consistent Hilbert.N := PLoN.Hilbert.consistent_of_FrameClass PLoN.AllFrameClass

instance : Canonical (Hilbert.N) (PLoN.AllFrameClass) := ⟨by tauto⟩

instance : Complete (Hilbert.N) (PLoN.AllFrameClass) := inferInstance

end Hilbert.N

end LO.Modal
