import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal.Neighborhood

variable {F : Frame}

def Frame.Supplementation (F : Frame) : Frame := Frame.mk_ℬ F.World (λ X => (Set.sUnion { ℬ Y | Y ⊆ X }))

local postfix:80 "♯" => Frame.Supplementation

lemma wow {w : F♯.World} : w ∈ ℬ X ↔ ∃ Y ⊆ X, w ∈ F.box Y := by
  simp only [Frame.Supplementation, Frame.box, Frame.mk_ℬ, Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and]

instance : F♯.IsMonotonic := by
  constructor;
  rintro X Y x hx;
  obtain ⟨W, hW₁, hW₂⟩ := wow.mp hx;
  constructor <;>
  . apply wow.mpr;
    use W;
    constructor;
    . tauto_set;
    . assumption;

instance [F.IsReflexive] : F♯.IsReflexive := by
  constructor;
  intro X w hw;
  replace ⟨Y, hY₁, hY₂⟩ := wow.mp hw;
  apply hY₁;
  apply F.refl;
  exact hY₂;

instance [F.IsTransitive] : F♯.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hY₁, hY₂⟩ := wow.mp hw;
  have := F.trans hY₂;
  sorry;

end LO.Modal.Neighborhood
