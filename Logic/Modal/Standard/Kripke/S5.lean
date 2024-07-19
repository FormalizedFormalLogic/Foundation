import Logic.Modal.Standard.Kripke.Geach
import Logic.Modal.Standard.Kripke.Preservation

namespace LO.Modal.Standard

namespace Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]

lemma Frame.PointGenerated.rel_universal
  {F : Kripke.Frame} {r : F.World} (F_refl : Reflexive F) (F_eucl : Euclidean F) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl F_eucl;
  simp [Frame.PointGenerated];
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply F_refl;
  . exact hy;
  . exact F_symm hx;
  . apply F_symm $ F_eucl hx hy;

abbrev UniversalFrameClass : FrameClass := { F | Universal F }

lemma iff_Universal_ReflexiveEuclidean_validOnFrameClass : UniversalFrameClass.{u}# ⊧ p ↔ ReflexiveEuclideanFrameClass.{u}# ⊧ p := by
  constructor;
  . intro h F hF V r;
    apply Model.PointGenerated.modal_equivalent_to_root ⟨F, V⟩ (by apply trans_of_refl_eucl hF.1 hF.2) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) ((⟨F, V⟩)↾r).Valuation;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

instance S5_complete_universal : Complete (𝐒𝟓 : DeductionParameter α) UniversalFrameClass.{u}# := ⟨by
  intro p hF;
  have : ReflexiveEuclideanFrameClass# ⊧ p := iff_Universal_ReflexiveEuclidean_validOnFrameClass.mp hF;
  exact S5_complete.complete this;
⟩

end Kripke

end LO.Modal.Standard
