import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Supplementation

namespace LO.Modal.Neighborhood

open Classical

variable {F : Frame}

def Frame.intersectionClosure (F : Frame) : Frame := {
  World := F.World,
  𝒩 a X := ∃ Xs : Finset _, Xs ≠ ∅ ∧ X = ⋂ Xi ∈ Xs, Xi ∧ ∀ Xi ∈ Xs, Xi ∈ F.𝒩 a
}

instance Frame.intersectionClosure.isRegular : F.intersectionClosure.IsRegular := by
  constructor;
  intro X Y a;
  simp only [intersectionClosure, ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp];
  rintro ⟨Xs, hXs₁, rfl, hX₂⟩ ⟨Ys, hYs₁, rfl, hY₂⟩;
  refine ⟨Xs ∪ Ys, ?_, ?_, ?_⟩;
  . simp only [Finset.union_eq_empty];
    grind;
  . ext b;
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union];
    grind;
  . simp only [Finset.mem_union];
    rintro Z (hZ | hZ);
    . apply hX₂; assumption;
    . apply hY₂; assumption;

lemma Frame.intersectionClosure.mem_box_of_mem_original_box {F : Frame} {x : F} {s : Set F} : x ∈ F.box s → x ∈ F.intersectionClosure.box s := by
  intro hx;
  use {s};
  refine ⟨?_, ?_, ?_⟩ <;> simp_all;

def Frame.quasiFiltering (F : Frame) : Frame := F.intersectionClosure.supplementation

namespace Frame.quasiFiltering

@[grind] lemma symm_𝒩 : F.quasiFiltering.𝒩 = F.supplementation.intersectionClosure.𝒩 := by
  dsimp [quasiFiltering];
  ext a X;
  simp [Frame.intersectionClosure, Frame.supplementation, Frame.mk_ℬ];
  constructor;
  . rintro ⟨_, hb₁, Y, hb₃, rfl, hb₅⟩;
    use Y;
    refine ⟨?_, ?_, ?_⟩;
    . assumption;
    . sorry;
    . tauto;
  . rintro ⟨Y, hY, rfl, hY₃⟩;
    use (⋂ Yi ∈ Y, Yi);
    refine ⟨?_, ?_⟩;
    . tauto;
    . use Y;
      refine ⟨?_, ?_, ?_⟩;
      . assumption;
      . rfl;
      . intro Yi hYi;
        obtain ⟨Z, hZ₁, hZ₂⟩ := hY₃ Yi hYi;
        have := @hZ₁ a;
        sorry;

lemma symm_box : F.quasiFiltering.box = F.supplementation.intersectionClosure.box := by
  ext x;
  simp [symm_𝒩];
  tauto;

instance isMonotonic : F.quasiFiltering.IsMonotonic := Frame.supplementation.isMonotonic

instance isRegular : F.quasiFiltering.IsRegular := Frame.supplementation.isRegular

instance isTransitive [F.IsTransitive] : F.quasiFiltering.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hY₁, Ys, hYs₁, rfl, hYs₂⟩ := Frame.supplementation.iff_exists_subset.mp hw;
  apply Frame.mono' (F := F.quasiFiltering) (X := (⋂ Yi ∈ Ys, F.box Yi)) $ by
    intro a ha;
    simp only [
      quasiFiltering, intersectionClosure, ne_eq, supplementation, box, mk_ℬ,
      Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and
    ];
    use (⋂ Yi ∈ Ys, Yi);
    refine ⟨?_, Ys, ?_, ?_, ?_⟩
    . assumption;
    . assumption;
    . tauto;
    . simpa [Frame.box] using ha;
  replace hYs₂ : w ∈ ⋂ Yi ∈ Ys, F.box^[2] Yi := by
    simp only [Set.mem_iInter];
    intro Yi hYi;
    apply F.trans $ hYs₂ Yi hYi;
  use F.intersectionClosure.box (⋂ Yi ∈ Ys, F.box Yi);
  constructor;
  . use (⋂ Yi ∈ Ys, F.box Yi);
  . use Ys.image F.box;
    refine ⟨?_, ?_, ?_⟩;
    . simpa [Finset.image_empty]
    . simp;
    . simp [Frame.box] at hYs₂ ⊢;
      simpa;

lemma mem_box_of_mem_original_box {F : Frame} {x : F} {s : Set F} : x ∈ F.box s → x ∈ F.quasiFiltering.box s := by
  intro hx;
  suffices x ∈ F.supplementation.intersectionClosure.box s by exact symm_box ▸ this;
  apply Frame.intersectionClosure.mem_box_of_mem_original_box;
  use F.box s;
  constructor;
  . use s;
  . assumption;

end Frame.quasiFiltering

end LO.Modal.Neighborhood
