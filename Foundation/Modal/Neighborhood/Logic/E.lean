import Foundation.Modal.Neighborhood.Hilbert

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood

namespace Neighborhood

abbrev FrameClass.E : FrameClass := Set.univ

end Neighborhood


namespace Hilbert.E.Neighborhood

instance : Sound Hilbert.E FrameClass.E := instSound_of_validates_axioms $ by simp;

instance : Entailment.Consistent Hilbert.E := consistent_of_sound_frameclass FrameClass.E $ by
  use ⟨Unit, λ _ => {}⟩;
  simp;

end Hilbert.E.Neighborhood


end LO.Modal
