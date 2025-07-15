import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

section

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.Cl 𝓢]

def MaximalConsistentSet.proofset (𝓢 : S) (φ : Formula α) : Set (MaximalConsistentSet 𝓢) := { Γ : MaximalConsistentSet 𝓢 | φ ∈ Γ }

namespace MaximalConsistentSet.proofset

local notation "‖" φ "‖" => MaximalConsistentSet.proofset 𝓢 φ

variable {φ ψ : Formula α}

lemma eq_top : ‖⊤‖ = Set.univ := by simp [proofset];

lemma eq_bot : ‖⊥‖ = ∅ := by simp [proofset];

lemma eq_neg : ‖∼φ‖ = ‖φ‖ᶜ := by simp [proofset]; tauto;

lemma eq_imp : ‖φ ➝ ψ‖ = (‖φ‖ᶜ ∪ ‖ψ‖) := by
  ext;
  simp [proofset];
  tauto;

lemma eq_and : ‖φ ⋏ ψ‖ = ‖φ‖ ∩ ‖ψ‖ := by simp [proofset]; tauto;

lemma eq_or : ‖φ ⋎ ψ‖ = ‖φ‖ ∪ ‖ψ‖ := by simp [proofset]; tauto;

attribute [simp, grind]
  eq_top
  eq_bot
  eq_neg
  eq_imp
  eq_and
  eq_or

@[grind]
lemma imp_subset : 𝓢 ⊢! φ ➝ ψ ↔ ‖φ‖ ⊆ ‖ψ‖ := by
  constructor;
  . intro h Γ;
    apply iff_mem_imp.mp $ iff_forall_mem_provable.mpr h Γ;
  . intro h;
    apply iff_forall_mem_provable.mp;
    intro Γ;
    apply iff_mem_imp.mpr $ @h Γ;

@[grind]
lemma iff_subset : 𝓢 ⊢! φ ⭤ ψ ↔ ‖φ‖ = ‖ψ‖ := by
  constructor;
  . intro h;
    apply Set.eq_of_subset_of_subset <;>
    . apply imp_subset.mp;
      cl_prover [h];
  . intro h;
    have ⟨h₁, h₂⟩ := Set.Subset.antisymm_iff.mp h;
    replace h₁ := imp_subset.mpr h₁;
    replace h₂ := imp_subset.mpr h₂;
    cl_prover [h₁, h₂];

lemma eq_boxed_of_eq [Entailment.E 𝓢] : ‖φ‖ = ‖ψ‖ → ‖□φ‖ = ‖□ψ‖ := by
  intro h;
  apply iff_subset.mp;
  apply re!;
  apply iff_subset.mpr;
  assumption;

end MaximalConsistentSet.proofset

end


section

namespace Neighborhood

open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Cl 𝓢] [Entailment.Consistent 𝓢]
variable {φ ψ ξ : Formula ℕ}

structure Canonicalℬ (𝓢 : S) where
  ℬ : Set (MaximalConsistentSet 𝓢) → Set (MaximalConsistentSet 𝓢)
  canonicity : ∀ φ, ℬ (proofset 𝓢 φ) = proofset 𝓢 (□φ)

instance : CoeFun (Canonicalℬ 𝓢) (fun _ => Set (MaximalConsistentSet 𝓢) → Set (MaximalConsistentSet 𝓢)) := ⟨Canonicalℬ.ℬ⟩

def mkCanonicalFrame
  (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢]
  (ℬ : Canonicalℬ 𝓢)
  : Frame := Frame.mk_ℬ (MaximalConsistentSet 𝓢) ℬ

def mkCanonicalModel
  (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢]
  (ℬ : Canonicalℬ 𝓢)
  : Model where
  toFrame := mkCanonicalFrame 𝓢 ℬ
  Val a := proofset 𝓢 (.atom a)

@[simp] lemma mkCanonicalModel.eq_ℬ_self : (mkCanonicalModel 𝓢 ℬ).ℬ = ℬ := by tauto;

lemma truthlemma : ↑(proofset 𝓢 φ) = ((mkCanonicalModel 𝓢 ℬ).truthset φ) := by
  induction φ with
  | hatom =>
    simp [mkCanonicalModel]
  | hfalsum =>
    simp [mkCanonicalModel]
  | himp φ ψ ihφ ihψ =>
    simp_all [MaximalConsistentSet.proofset.eq_imp, ←ihφ, ←ihψ];
  | hbox φ ihφ =>
    rw [Model.truthset.eq_box, ←ihφ, mkCanonicalModel.eq_ℬ_self, (@ℬ.canonicity φ)];

lemma complete_of_canonical_frame
  (C : FrameClass) (ℬ)
  (hC : (mkCanonicalFrame 𝓢 ℬ) ∈ C)
  : LO.Complete 𝓢 C := by
  constructor;
  intro φ;
  contrapose!;
  intro hφ;
  have := FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum this;
  apply not_validOnFrameClass_of_exists_model_world;
  use (mkCanonicalModel 𝓢 ℬ), Γ;
  constructor;
  . assumption;
  . simp only [Semantics.Realize, Satisfies, ←truthlemma];
    suffices Γ ∈ (proofset 𝓢 (∼φ)) by simpa;
    apply hΓ;
    tauto;

open Classical in
def canonical_minimal_ℬ (𝓢 : S) [Entailment.E 𝓢] : Canonicalℬ 𝓢 where
  ℬ Γ := if h : ∃ φ, Γ = (proofset 𝓢 φ) then (proofset 𝓢 (□(h.choose))) else ∅
  canonicity := by
    intro φ;
    split;
    . rename_i h;
      apply proofset.eq_boxed_of_eq;
      apply h.choose_spec.symm;
    . tauto;

end Neighborhood

end

end LO.Modal
