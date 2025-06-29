import Foundation.Modal.PLoN.Hilbert
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

instance : Entailment.Consistent Logic.N := PLoN.Hilbert.consistent_of_FrameClass PLoN.AllFrameClass

instance : Canonical (Logic.N) (PLoN.AllFrameClass) := ⟨by tauto⟩

instance : Complete (Logic.N) (PLoN.AllFrameClass) := inferInstance

end Hilbert.N

end LO.Modal
