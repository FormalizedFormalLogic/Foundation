import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal

open LO.Entailment


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

end MaximalConsistentSet.proofset

end


section

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Cl 𝓢]

namespace Neighborhood

open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet

variable {φ ψ ξ : Formula ℕ}

class Frame.IsCanonical (𝓢 : S) (F : Frame) where
  def_equiv : F.World = (MaximalConsistentSet 𝓢)
  def_ℬ : ∀ φ, (F.ℬ (def_equiv ▸ (proofset 𝓢 φ))) = (def_equiv ▸ proofset 𝓢 (□φ))

variable {F : Frame} [canonical : F.IsCanonical 𝓢]

abbrev canonicalModel (𝓢 : S) (F : Frame) [canonical : F.IsCanonical 𝓢] : Model where
  toFrame := F
  Val a := canonical.def_equiv ▸ proofset 𝓢 (.atom a)

instance : Coe (Set (MaximalConsistentSet 𝓢)) (Set (canonicalModel 𝓢 F).World) := ⟨λ Γ => canonical.def_equiv ▸ Γ⟩

@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel 𝓢 F).World := Formula.Neighborhood.Satisfies.semantics (M := canonicalModel 𝓢 F)

set_option pp.proofs true

lemma truthlemma : ↑(proofset 𝓢 φ) = ((canonicalModel 𝓢 F).truthset φ) := by
  induction φ with
  | hatom => simp
  | hfalsum =>
    sorry;
  | himp φ ψ ihφ ihψ =>
    simp_all [MaximalConsistentSet.proofset.eq_imp, ←ihφ, ←ihψ];
    sorry;
  | hbox φ ihφ =>
    rw [Model.truthset.eq_box, ←ihφ, canonical.def_ℬ];

lemma complete_of_canonical_frame
  (C : FrameClass)
  (F : Frame) [F_canonical : F.IsCanonical 𝓢] (hFC : F ∈ C)
  : LO.Complete 𝓢 C := by
  constructor;
  intro φ;
  contrapose!;
  intro hφ;
  have := FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum this;
  apply not_validOnFrameClass_of_exists_model_world;
  use (canonicalModel 𝓢 F), (F_canonical.def_equiv ▸ Γ);
  constructor;
  . apply hFC;
  . simp only [Semantics.Realize, Satisfies, ←truthlemma];
    suffices Γ ∉ proofset 𝓢 φ by
      sorry;
    simpa [proofset, ←iff_mem_neg] using hΓ;

end Neighborhood

end

end LO.Modal
