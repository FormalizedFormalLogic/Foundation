import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal.Neighborhood

variable {F : Frame}

def Frame.supplementation (F : Frame) : Frame where
  World := F.World
  𝒩 a X := ∃ Y ⊆ X, a ∈ F.box Y

namespace Frame.supplementation

lemma iff_exists_subset {X : Set (F.World)} {w : F.World} : w ∈ F.supplementation.box X ↔ ∃ Y ⊆ X, w ∈ F.box Y := by
  simp [Frame.supplementation];
  tauto;

lemma mem_box_of_mem_original_box : x ∈ F.box X → x ∈ F.supplementation.box X := by
  intro hx;
  use X;

lemma box_aux {X : Set (F.World)} : F.supplementation.box X = ⋃₀ {x | ∃ Y ⊆ X, F.box Y = x} := by
  ext w;
  simp only [supplementation, Set.mem_setOf_eq, Set.mem_sUnion, exists_exists_and_eq_and]
  constructor;
  . rintro ⟨Y, hY₁, hY₂⟩; use Y;
  . rintro ⟨Y, hY₁, hY₂⟩; use Y;

lemma subset (X : Set (F.World)) : F.box X ⊆ F.supplementation.box X := by
  intro x _;
  use X;

lemma monotonic {X Y : Set (F.World)} (h : X ⊆ Y) : F.supplementation.box X ⊆ F.supplementation.box Y := by
  intro x hX;
  obtain ⟨X', hX', hX⟩ := iff_exists_subset.mp hX;
  apply iff_exists_subset.mpr;
  use X';
  constructor;
  . apply Set.Subset.trans hX' h;
  . assumption;

lemma monotonic_iterated {X Y : Set (F.World)} (h : X ⊆ Y) (n) : F.supplementation.box^[n] X ⊆ F.supplementation.box^[n] Y := by
  induction n with
  | zero => simpa;
  | succ n ih =>
    rw [Function.iterate_succ'];
    apply monotonic;
    apply ih;

lemma itl_reduce : F.supplementation.supplementation.box X = F.supplementation.box X := by
  ext x;
  constructor;
  . rintro ⟨Y, RYX, Z, RZY, hZ⟩;
    use Z;
    constructor;
    . tauto_set;
    . assumption;
  . apply subset;

instance isMonotonic : F.supplementation.IsMonotonic := by
  constructor;
  rintro X Y x hx;
  obtain ⟨W, hW₁, hW₂⟩ := iff_exists_subset.mp hx;
  constructor <;>
  . apply iff_exists_subset.mpr;
    use W;
    constructor;
    . tauto_set;
    . assumption;

instance isReflexive [F.IsReflexive] : F.supplementation.IsReflexive := by
  constructor;
  intro X w hw;
  replace ⟨Y, hY₁, hY₂⟩ := iff_exists_subset.mp hw;
  apply hY₁;
  apply F.refl;
  exact hY₂;

instance containsUnit [F.ContainsUnit] : F.supplementation.ContainsUnit := by
  constructor;
  ext x;
  suffices ∃ Y ⊆ Set.univ, Y ∈ F.𝒩 x by
    simp only [supplementation, Set.mem_setOf_eq, Set.mem_univ, iff_true];
    exact this;
  use Set.univ;
  constructor;
  . rfl;
  . simp;

instance isTransitive [F.IsTransitive] : F.supplementation.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hYX, hY⟩ := iff_exists_subset.mp hw;
  apply monotonic_iterated hYX 2
  apply monotonic $ subset Y;
  apply subset (F.box Y) $ F.trans hY;

instance isRegular [F.IsRegular] : F.supplementation.IsRegular := by
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

end Frame.supplementation


section

open MaximalConsistentSet (proofset)
open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet
open MaximalConsistentSet.proofset

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.EM 𝓢] [Entailment.Consistent 𝓢]

abbrev maximalCanonicity (𝓢 : S) [Entailment.EM 𝓢] [Entailment.Consistent 𝓢] : Canonicity 𝓢 where
  𝒩 := (minimalCanonicity 𝓢).toModel.supplementation.𝒩
  def_𝒩 := by
    intro X φ;
    constructor;
    . rintro h;
      use proofset 𝓢 φ;
      constructor;
      . simp;
      . use φ;
        constructor;
        . rfl;
        . grind;
    . rintro ⟨Y, hψ₁, ⟨ψ, rfl, hψ₂⟩⟩;
      apply proofset.box_subset_of_subset hψ₁ hψ₂;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

instance : (maximalCanonicity 𝓢).toModel.IsMonotonic := Frame.supplementation.isMonotonic (F := (minimalCanonicity 𝓢).toModel.toFrame)

instance [Entailment.HasAxiomC 𝓢] : (maximalCanonicity 𝓢).toModel.IsRegular := Frame.supplementation.isRegular (F := (minimalCanonicity 𝓢).toModel.toFrame)

instance [Entailment.HasAxiomN 𝓢] : (maximalCanonicity 𝓢).toModel.ContainsUnit := Frame.supplementation.containsUnit (F := (minimalCanonicity 𝓢).toModel.toFrame)

instance [Entailment.HasAxiomT 𝓢] : (maximalCanonicity 𝓢).toModel.IsReflexive := Frame.supplementation.isReflexive (F := (minimalCanonicity 𝓢).toModel.toFrame)

instance [Entailment.HasAxiomFour 𝓢] : (maximalCanonicity 𝓢).toModel.IsTransitive := Frame.supplementation.isTransitive (F := (minimalCanonicity 𝓢).toModel.toFrame)

end



end LO.Modal.Neighborhood
