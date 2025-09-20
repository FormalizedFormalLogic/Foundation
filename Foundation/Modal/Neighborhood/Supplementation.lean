import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal.Neighborhood

variable {F : Frame}

def Frame.Supplementation (F : Frame) : Frame := Frame.mk_ℬ F.World (λ X => (Set.sUnion { F.box Y | Y ⊆ X }))

local postfix:80 "♯" => Frame.Supplementation

namespace Frame.Supplementation

lemma iff_exists_subset {X : Set (F.World)} {w : F.World} : w ∈ F♯.box X ↔ ∃ Y ⊆ X, w ∈ F.box Y := by
  simp [Frame.Supplementation, Frame.box, Frame.mk_ℬ, Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and]

lemma subset (X : Set (F.World)) : F.box X ⊆ F♯.box X := by
  intro x;
  simp [Frame.Supplementation, Frame.box, Frame.mk_ℬ];
  tauto;

lemma monotonic {X Y : Set (F.World)} (h : X ⊆ Y) : F♯.box X ⊆ F♯.box Y := by
  intro x hX;
  obtain ⟨X', hX', hX⟩ := iff_exists_subset.mp hX;
  apply iff_exists_subset.mpr;
  use X';
  constructor;
  . apply Set.Subset.trans hX' h;
  . assumption;

lemma monotonic_iterated {X Y : Set (F.World)} (h : X ⊆ Y) (n) : F♯.box^[n] X ⊆ F♯.box^[n] Y := by
  induction n with
  | zero => simpa;
  | succ n ih =>
    rw [Function.iterate_succ'];
    apply monotonic;
    apply ih;

lemma itl_reduce : F♯♯.box X = F♯.box X := by
  ext x;
  simp only [Supplementation, mk_ℬ, Set.mem_setOf_eq, Set.mem_sUnion, exists_exists_and_eq_and]
  constructor;
  . rintro ⟨Y, RYX, Z, RZY, hZ⟩;
    use Z;
    constructor;
    . tauto_set;
    . assumption;
  . tauto;

instance : F♯.IsMonotonic := by
  constructor;
  rintro X Y x hx;
  obtain ⟨W, hW₁, hW₂⟩ := iff_exists_subset.mp hx;
  constructor <;>
  . apply iff_exists_subset.mpr;
    use W;
    constructor;
    . tauto_set;
    . assumption;

instance [F.IsReflexive] : F♯.IsReflexive := by
  constructor;
  intro X w hw;
  replace ⟨Y, hY₁, hY₂⟩ := iff_exists_subset.mp hw;
  apply hY₁;
  apply F.refl;
  exact hY₂;

instance [F.ContainsUnit] : F♯.ContainsUnit := by
  constructor;
  ext x;
  suffices ∃ a, a ∈ F.𝒩 x by simpa [Supplementation, mk_ℬ];
  use Set.univ;
  simp;

instance [F.IsTransitive] : F♯.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hYX, hY⟩ := iff_exists_subset.mp hw;
  apply monotonic_iterated hYX 2
  apply monotonic $ subset Y;
  apply subset (F.box Y) $ F.trans hY;

instance [F.IsRegular] : F♯.IsRegular := by
  constructor;
  rintro X Y w ⟨hX, hY⟩;
  apply iff_exists_subset.mpr;
  obtain ⟨X', _⟩ := iff_exists_subset.mp hX;
  obtain ⟨Y', _⟩ := iff_exists_subset.mp hY;
  use X' ∩ Y';
  constructor;
  . tauto_set;
  . apply @Frame.regular F _ X' Y';
    tauto;

end Frame.Supplementation


section

open MaximalConsistentSet (proofset)
open MaximalConsistentSet.proofset

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

abbrev maximalCanonicalFrame (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Frame := (minimalCanonicalFrame 𝓢)♯

variable [Entailment.EM 𝓢]

instance : (maximalCanonicalFrame 𝓢).IsCanonical 𝓢 where
  box_proofset := by
    intro φ;
    apply Set.eq_of_subset_of_subset;
    . intro Γ;
      simp only [
        Frame.Supplementation, Frame.mk_ℬ, Set.mem_setOf_eq, Set.mem_sUnion,
        exists_exists_and_eq_and, forall_exists_index, and_imp
      ];
      intro X hX h;
      split at h;
      . rename_i hψ;
        rw [hψ.choose_spec] at hX;
        apply box_subset_of_subset hX;
        apply h;
      . contradiction;
    . intro Γ;
      simp only [
        Frame.Supplementation, Frame.mk_ℬ, Set.mem_setOf_eq, Set.mem_sUnion,
        exists_exists_and_eq_and
      ];
      intro hΓ;
      use proofset 𝓢 φ;
      constructor
      . rfl;
      . split;
        . rename_i hψ;
          rw [←eq_boxed_of_eq hψ.choose_spec];
          apply hΓ;
        . simp_all;

end


end LO.Modal.Neighborhood
