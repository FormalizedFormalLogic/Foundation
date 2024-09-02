import Logic.Modal.Standard.Kripke.Geach
import Logic.Modal.Standard.Kripke.Preservation

namespace LO.Modal.Standard

open LO.Kripke

namespace Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]

lemma iff_Universal_ReflexiveEuclidean_validOnFrameClass : UniversalFrameClass.{u}#α ⊧ p ↔ ReflexiveEuclideanFrameClass.{u}#α ⊧ p := by
  constructor;
  . intro h F hF V r;
    apply modal_equivalent_at_root_on_generated_model ⟨F, V⟩ (by apply trans_of_refl_eucl hF.1 hF.2) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) ((⟨F, V⟩)↾r).Valuation;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

instance S5_complete_universal : Complete 𝐒𝟓 (UniversalFrameClass.{u}#α) := ⟨by
  intro p hF;
  exact S5_complete.complete $ iff_Universal_ReflexiveEuclidean_validOnFrameClass.mp hF;
⟩

end Kripke

end LO.Modal.Standard
