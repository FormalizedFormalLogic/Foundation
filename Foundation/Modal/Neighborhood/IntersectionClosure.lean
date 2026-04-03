module

public import Foundation.Modal.Neighborhood.Supplementation

@[expose] public section

namespace LO.Modal.Neighborhood

open Classical

variable {F : Frame}

def Frame.intersectionClosure (F : Frame) : Frame := {
  World := F.World,
  𝒩 a X := ∃ Xs : Finset (Set F.World), Xs ≠ ∅ ∧ X = ⋂ Xi ∈ Xs, Xi ∧ ∀ Xi ∈ Xs, Xi ∈ F.𝒩 a
}

instance Frame.intersectionClosure.isRegular : F.intersectionClosure.IsRegular := by
  constructor;
  intro X Y a;
  unfold intersectionClosure;
  simp only [ne_eq, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp];
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

lemma symm_𝒩 : F.quasiFiltering.𝒩 = F.supplementation.intersectionClosure.𝒩 := by
  dsimp [quasiFiltering];
  ext w X;
  constructor;
  . rintro ⟨_, hYs₃, ⟨Ys, hYs₁, rfl, hYs₂⟩⟩;
    let Y := ⋂ Yi ∈ Ys, Yi;
    have : X = ⋂ Yi ∈ Ys, Yi ∪ (X \ Y) := calc
      _ = Y ∪ (X \ Y) := by
        ext x;
        constructor;
        . tauto;
        . rintro (h | ⟨h, _⟩);
          . apply hYs₃ h;
          . assumption;
      _ = _ := by
        ext x;
        simp [Y];
        grind;
    rw [this];
    use Ys.image (λ Yi => Yi ∪ (X \ Y));
    refine ⟨?_, ?_, ?_⟩;
    . simpa;
    . simp; rfl;
    . intro Yi hYi;
      use Yi;
      constructor;
      . rfl;
      . apply hYs₂;
        simp at hYi;



        sorry;
        -- assumption;
  . rintro ⟨Ys, hYs₁, rfl, hYs₂⟩;
    let Zs := Finset.image (α := Ys) (λ ⟨Yi, hYi⟩ => hYs₂ Yi hYi |>.choose) Finset.univ;
    use (⋂ Zi ∈ Zs, Zi);
    constructor;
    . rintro a ha _ ⟨Y, _, rfl⟩;
      suffices Y ∈ Ys → a ∈ Y by simpa;
      rintro hY;
      apply hYs₂ Y hY |>.choose_spec |>.1;
      simp only [Set.mem_setOf_eq, Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Set.iInter_exists, Set.mem_iInter, Zs] at ha;
      apply ha;
      . rfl;
      . assumption;
    . use Zs;
      refine ⟨?_, ?_, ?_⟩;
      . simpa [Zs];
      . rfl;
      . simp [Zs];
        rintro _ Yi hYi rfl;
        apply hYs₂ Yi hYi |>.choose_spec |>.2;

lemma symm_box : F.quasiFiltering.box = F.supplementation.intersectionClosure.box := by
  ext x;
  simp [symm_𝒩];
  rfl;

instance isMonotonic : F.quasiFiltering.IsMonotonic := Frame.supplementation.isMonotonic

instance isRegular : F.quasiFiltering.IsRegular := Frame.supplementation.isRegular

instance isTransitive [F.IsTransitive] : F.quasiFiltering.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hY₁, Ys, hYs₁, rfl, hYs₂⟩ := Frame.supplementation.iff_exists_subset.mp hw;
  apply Frame.mono' (F := F.quasiFiltering) (X := (⋂ Yi ∈ Ys, F.box Yi)) $ by
    intro a ha;
    use (⋂ Yi ∈ Ys, Yi);
    refine ⟨?_, Ys, ?_, ?_, ?_⟩
    . assumption;
    . assumption;
    . tauto;
    . simpa [Frame.box] using ha;
  replace hYs₂ : w ∈ ⋂ Yi ∈ Ys, F.box^[2] Yi := by
    apply Set.mem_iInter.mpr;
    rintro Yi _ ⟨_, rfl⟩;
    apply F.trans;
    apply hYs₂ Yi;
    assumption;
  use (⋂ Yi ∈ Ys, F.box Yi);
  constructor;
  . rfl;
  . use Ys.image F.box
    refine ⟨?_, ?_, ?_⟩;
    . simpa;
    . simp; rfl;
    .
      sorry;
      -- simp [Frame.box] at hYs₂ ⊢;

instance containsUnit [F.ContainsUnit] : F.quasiFiltering.ContainsUnit := by
  constructor;
  ext x;
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true];
  use Set.univ;
  constructor;
  . rfl;
  . use {Set.univ};
    simp;
    rfl;

lemma mem_box_of_mem_original_box {x : F} {s : Set F} : x ∈ F.box s → x ∈ F.quasiFiltering.box s := by
  intro hx;
  suffices x ∈ F.supplementation.intersectionClosure.box s by exact symm_box ▸ this;
  apply Frame.intersectionClosure.mem_box_of_mem_original_box;
  apply Frame.supplementation.mem_box_of_mem_original_box;
  exact hx;

end Frame.quasiFiltering

end LO.Modal.Neighborhood
end
