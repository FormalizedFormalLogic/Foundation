import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Entailment.EM

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

section

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.Cl 𝓢]

def MaximalConsistentSet.proofset (𝓢 : S) (φ : Formula α) : Set (MaximalConsistentSet 𝓢) := { Γ : MaximalConsistentSet 𝓢 | φ ∈ Γ }

namespace MaximalConsistentSet.proofset

local notation "‖" φ "‖" => MaximalConsistentSet.proofset 𝓢 φ

variable {φ ψ : Formula α} {Γ : MaximalConsistentSet 𝓢}

omit [DecidableEq α] [Entailment.Cl 𝓢] in
@[grind]
lemma iff_mem : φ ∈ Γ ↔ Γ ∈ ‖φ‖ := by simp [proofset];

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

lemma iff_provable_eq_univ : 𝓢 ⊢ φ ↔ ‖φ‖ = Set.univ := by
  constructor;
  . intro h;
    apply Set.eq_univ_of_forall;
    intro Γ;
    apply iff_mem.mp;
    grind;
  . intro h;
    apply iff_forall_mem_provable.mp;
    intro Γ;
    apply iff_mem.mpr;
    rw [h];
    tauto;

@[grind]
lemma imp_subset : 𝓢 ⊢ φ ➝ ψ ↔ ‖φ‖ ⊆ ‖ψ‖ := by
  constructor;
  . intro h Γ;
    apply iff_mem_imp.mp $ iff_forall_mem_provable.mpr h Γ;
  . intro h;
    apply iff_forall_mem_provable.mp;
    intro Γ;
    apply iff_mem_imp.mpr $ @h Γ;

@[grind]
lemma iff_subset : 𝓢 ⊢ φ ⭤ ψ ↔ ‖φ‖ = ‖ψ‖ := by
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

@[grind]
lemma box_subset_of_subset [Entailment.EM 𝓢] : ‖φ‖ ⊆ ‖ψ‖ → ‖□φ‖ ⊆ ‖□ψ‖ := by
  suffices 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! □φ ➝ □ψ by simpa [imp_subset];
  apply Entailment.rm!;

end MaximalConsistentSet.proofset

end


namespace Neighborhood

open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.E 𝓢] [Entailment.Consistent 𝓢]
variable {φ ψ ξ : Formula ℕ}

open Classical in
abbrev minimalCanonicalFrame (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Frame := Frame.mk_ℬ
  (MaximalConsistentSet 𝓢)
  (λ X => if h : ∃ φ, X = (proofset 𝓢 φ) then (proofset 𝓢 (□(h.choose))) else ∅)

namespace minimalCanonicalFrame

@[grind]
lemma box_proofset : (minimalCanonicalFrame 𝓢).box (proofset 𝓢 φ) = (proofset 𝓢 (□φ)) := by
  dsimp [minimalCanonicalFrame, Frame.mk_ℬ, Frame.box];
  split_ifs with h;
  . apply proofset.eq_boxed_of_eq;
    apply h.choose_spec.symm;
  . tauto;

@[grind]
lemma multibox_proofset : (minimalCanonicalFrame 𝓢).box^[n] (proofset 𝓢 φ) = (proofset 𝓢 (□^[n]φ)) := by
  induction n generalizing φ with
  | zero => simp;
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, box_proofset, ih];

lemma exists_box (X) (Γ : (minimalCanonicalFrame 𝓢).World) (hΓ : Γ ∈ Frame.box _ X)
  : ∃ φ, X = proofset 𝓢 φ ∧ Frame.box _ X = proofset 𝓢 (□φ)
  := by
    dsimp [minimalCanonicalFrame, Frame.mk_ℬ, Frame.box] at hΓ;
    split_ifs at hΓ with hφ;
    . obtain ⟨φ, rfl⟩ := hφ;
      use φ;
      grind;
    . contradiction;

end minimalCanonicalFrame

abbrev minimalCanonicalModel (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Model where
  toFrame := minimalCanonicalFrame 𝓢
  Val a := proofset 𝓢 (.atom a)

@[grind]
lemma minimalCanonicalModel.truthlemma : (proofset 𝓢 φ) = ((minimalCanonicalModel 𝓢) φ) := by
  induction φ with
  | hatom => simp [minimalCanonicalModel]
  | hfalsum => simp [minimalCanonicalModel];
  | himp φ ψ ihφ ihψ => simp_all [MaximalConsistentSet.proofset.eq_imp];
  | hbox φ ihφ => simp [Model.truthset.eq_box, ←ihφ, minimalCanonicalFrame.box_proofset];

lemma minimalCanonicalFrame.completeness {C : FrameClass} (hC : (minimalCanonicalFrame 𝓢) ∈ C) : LO.Complete 𝓢 C := by
  constructor;
  intro φ hφ;
  contrapose! hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum $ FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  apply not_validOnFrameClass_of_exists_model_world;
  use (minimalCanonicalModel 𝓢), Γ;
  constructor;
  . assumption;
  . suffices Γ ∉ proofset 𝓢 φ by simpa [Semantics.Realize, Satisfies, minimalCanonicalModel.truthlemma];
    apply MaximalConsistentSet.proofset.iff_mem.not.mp;
    apply MaximalConsistentSet.iff_mem_neg.mp;
    tauto;

end Neighborhood


end LO.Modal
