import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal.Neighborhood

variable {F : Frame}

def Frame.supplementation (F : Frame) : Frame := Frame.mk_ℬ F.World (λ X => (Set.sUnion { F.box Y | Y ⊆ X }))

namespace Frame.supplementation

lemma iff_exists_subset {X : Set (F.World)} {w : F.World} : w ∈ F.supplementation.box X ↔ ∃ Y ⊆ X, w ∈ F.box Y := by
  simp [Frame.supplementation, Frame.box, Frame.mk_ℬ, Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and]

lemma subset (X : Set (F.World)) : F.box X ⊆ F.supplementation.box X := by
  intro x;
  simp [Frame.supplementation, Frame.box, Frame.mk_ℬ];
  tauto;

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
  simp only [supplementation, mk_ℬ, Set.mem_setOf_eq, Set.mem_sUnion, exists_exists_and_eq_and]
  constructor;
  . rintro ⟨Y, RYX, Z, RZY, hZ⟩;
    use Z;
    constructor;
    . tauto_set;
    . assumption;
  . tauto;

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

instance [F.ContainsUnit] : F.supplementation.ContainsUnit := by
  constructor;
  ext x;
  suffices ∃ a, a ∈ F.𝒩 x by simpa [supplementation, mk_ℬ];
  use Set.univ;
  simp;

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

abbrev maximalCanonicalFrame (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Frame := (minimalCanonicalFrame 𝓢).supplementation

namespace maximalCanonicalFrame

open Classical in
lemma box_proofset : Frame.box (maximalCanonicalFrame 𝓢) (proofset 𝓢 φ) = proofset 𝓢 (□φ) := by
  ext Γ;
  suffices (∃ a ⊆ proofset 𝓢 φ, Γ ∈ if h : ∃ φ, a = proofset 𝓢 φ then proofset 𝓢 (□h.choose) else ∅) ↔ Γ ∈ proofset 𝓢 (□φ) by
    simpa [maximalCanonicalFrame, minimalCanonicalFrame, Frame.mk_ℬ, Frame.supplementation];
  constructor;
  . rintro ⟨X, hX₁, hX₂⟩;
    split_ifs at hX₂ with hX;
    . apply box_subset_of_subset (hX.choose_spec ▸ hX₁);
      exact hX₂;
    . contradiction;
  . intro hΓ;
    use proofset 𝓢 φ;
    constructor;
    . tauto;
    . split_ifs with h;
      . exact eq_boxed_of_eq h.choose_spec ▸ hΓ;
      . push_neg at h;
        tauto;

end maximalCanonicalFrame


abbrev maximalCanonicalModel (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Model where
  toFrame := maximalCanonicalFrame 𝓢
  Val a := proofset 𝓢 (.atom a)

@[grind]
protected lemma maximalCanonicalModel.truthlemma : (proofset 𝓢 φ) = ((maximalCanonicalModel 𝓢) φ) := by
  induction φ with
  | hatom => simp [maximalCanonicalModel]
  | hfalsum => simp [maximalCanonicalModel];
  | himp φ ψ ihφ ihψ => simp_all [MaximalConsistentSet.proofset.eq_imp];
  | hbox φ ihφ => simp [Model.truthset.eq_box, ←ihφ, maximalCanonicalFrame.box_proofset];

protected lemma maximalCanonicalFrame.completeness {C : FrameClass} (hC : (maximalCanonicalFrame 𝓢) ∈ C) : LO.Complete 𝓢 C := by
  constructor;
  intro φ hφ;
  contrapose! hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum $ FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  apply not_validOnFrameClass_of_exists_model_world;
  use (maximalCanonicalModel 𝓢), Γ;
  constructor;
  . assumption;
  . suffices Γ ∉ proofset 𝓢 φ by simpa [Semantics.Realize, Satisfies, maximalCanonicalModel.truthlemma];
    apply MaximalConsistentSet.proofset.iff_mem.not.mp;
    apply MaximalConsistentSet.iff_mem_neg.mp;
    tauto;


end

end LO.Modal.Neighborhood
