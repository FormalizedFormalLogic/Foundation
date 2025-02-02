import Foundation.Modal.Kripke2.AxiomGeach
import Foundation.Modal.Kripke2.Preservation

namespace LO.Modal

namespace Kripke

abbrev UniversalFrameClass : FrameClass := { F | Universal F }

lemma iff_Universal_ReflexiveEuclidean_validOnFrameClass : UniversalFrameClass ⊧ φ ↔ ReflexiveEuclideanFrameClass ⊧ φ := by
  constructor;
  . intro h F hF V r;
    let M : Model := ⟨F, V⟩;
    apply Model.PointGenerated.modal_equivalent_at_root  (M := ⟨F, V⟩) (by apply trans_of_refl_eucl hF.1 hF.2) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) (M↾r).Val;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

end Kripke

end LO.Modal
