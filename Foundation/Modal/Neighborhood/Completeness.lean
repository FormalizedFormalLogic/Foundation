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

lemma iff_provable_eq_univ : 𝓢 ⊢! φ ↔ ‖φ‖ = Set.univ := by
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

@[grind]
lemma box_subset_of_subset [Entailment.EM 𝓢] : ‖φ‖ ⊆ ‖ψ‖ → ‖□φ‖ ⊆ ‖□ψ‖ := by
  intro h;
  apply imp_subset.mp;
  exact Entailment.rm! $ imp_subset.mpr h;

end MaximalConsistentSet.proofset

end


section

namespace Neighborhood

open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} -- [Entailment.Cl 𝓢] [Entailment.Consistent 𝓢]
variable {φ ψ ξ : Formula ℕ}

class Frame.IsCanonical (F : Frame) (𝓢 : S) : Prop where
  eq_world : F.World = MaximalConsistentSet 𝓢 := by rfl
  box_proofset : ∀ φ, F.box (eq_world ▸ (proofset 𝓢 φ)) = eq_world ▸ (proofset 𝓢 (□φ))

namespace Frame.IsCanonical

variable {F : Frame} [canonical : F.IsCanonical 𝓢]

@[simp]
lemma eq_empty : (canonical.eq_world ▸ (∅ : Set (MaximalConsistentSet 𝓢))) = ∅ := by
  have := canonical.eq_world;
  grind;

@[simp]
lemma eq_union {X Y : Set (MaximalConsistentSet 𝓢)} : (canonical.eq_world ▸ (X ∪ Y)) = ((canonical.eq_world ▸ X) ∪ (canonical.eq_world ▸ Y)) := by
  have := canonical.eq_world;
  grind;

@[simp]
lemma eq_comp {X : Set (MaximalConsistentSet 𝓢)} : (canonical.eq_world ▸ Xᶜ) = (canonical.eq_world ▸ X)ᶜ := by
  haveI := canonical.eq_world;
  grind;

@[simp]
lemma iff_mem {Γ : MaximalConsistentSet 𝓢} {X : Set _} : Γ ∈ X ↔ (canonical.eq_world ▸ Γ) ∈ (canonical.eq_world ▸ X) := by
  have := canonical.eq_world;
  grind;

end Frame.IsCanonical


def canonicalModel (F : Frame) (𝓢 : S) [canonical : F.IsCanonical 𝓢] : Model where
  toFrame := F
  Val a := canonical.eq_world ▸ proofset 𝓢 (.atom a)

namespace canonicalModel

variable {F : Frame} [canonical : F.IsCanonical 𝓢]

@[simp] lemma eq_model_box : (canonicalModel F 𝓢).box = F.box := by tauto;

end canonicalModel

variable [Entailment.Cl 𝓢]
         {F : Frame} [canonical : F.IsCanonical 𝓢]

lemma truthlemma : canonical.eq_world ▸ (proofset 𝓢 φ) = ((canonicalModel F 𝓢).truthset φ) := by
  induction φ with
  | hatom => simp [canonicalModel]
  | hfalsum => simp [canonicalModel];
  | himp φ ψ ihφ ihψ => simp_all [MaximalConsistentSet.proofset.eq_imp, ←ihφ, ←ihψ];
  | hbox φ ihφ =>
    rw [Model.truthset.eq_box, ←ihφ, ←(canonical.box_proofset φ)];
    rfl;

lemma complete_of_canonical_frame (C : FrameClass) (F : Frame) [canonical : F.IsCanonical 𝓢] (hC : F ∈ C)
  : LO.Complete 𝓢 C := by
  constructor;
  intro φ;
  contrapose!;
  intro hφ;
  have := FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum this;
  apply not_validOnFrameClass_of_exists_model_world;
  use (canonicalModel F 𝓢), (canonical.eq_world ▸ Γ);
  constructor;
  . assumption;
  . simp only [Semantics.Realize, Satisfies, ←truthlemma];
    suffices Γ ∈ (proofset 𝓢 (∼φ)) by
      apply canonical.iff_mem.not.mp;
      simpa using this;
    apply hΓ;
    tauto;




open Classical in
abbrev minimalCanonicalFrame (𝓢 : S) [Entailment.E 𝓢] [Entailment.Consistent 𝓢] : Frame := Frame.mk_ℬ
  (MaximalConsistentSet 𝓢)
  (λ X => if h : ∃ φ, X = (proofset 𝓢 φ) then (proofset 𝓢 (□(h.choose))) else ∅)

namespace minimalCanonicalFrame

variable {𝓢 : S} [Entailment.E 𝓢] [Entailment.Consistent 𝓢]


instance : (minimalCanonicalFrame 𝓢).IsCanonical 𝓢 where
  box_proofset := by
    intro φ;
    dsimp [minimalCanonicalFrame, Frame.mk_ℬ, Frame.box];
    split;
    . rename_i h;
      apply proofset.eq_boxed_of_eq;
      apply h.choose_spec.symm;
    . tauto;

lemma exists_box (X) (Γ : (minimalCanonicalFrame 𝓢).World) (hΓ : Γ ∈ Frame.box _ X)
  : ∃ φ, X = proofset 𝓢 φ ∧ Frame.box _ X = proofset 𝓢 (□φ)
  := by
    simp [Frame.mk_ℬ, Frame.box] at hΓ;
    split at hΓ;
    . rename_i h;
      obtain ⟨φ, hφ⟩ := h;
      use φ;
      constructor;
      . assumption;
      . convert Frame.IsCanonical.box_proofset (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) φ;
    . contradiction;

/-
lemma exists_dia (X) (Γ : (CanonicalBox.minimal 𝓢).model.World) (hΓ : Γ ∈ Frame.box _ X)
  : ∃ φ, X = proofset 𝓢 φ ∧ Frame.dia _ X = proofset 𝓢 (◇φ)
  := by
    obtain ⟨φ, hφ, hΓ⟩ := exists_box X Γ hΓ;
    use φ;
    constructor;
    . assumption;
    . ext Γ;
      rw [(show ◇φ = ∼□(∼φ) by rfl)];
      simp only [
        CanonicalBox.minimal, CanonicalBox.model, CanonicalBox.frame, Frame.mk_ℬ,
        Frame.dia, Frame.box, Set.mem_setOf_eq, Set.setOf_mem_eq, Set.mem_compl_iff,
        proofset.eq_neg
      ];
      constructor;
      . intro h;
        split at h;
        . rename_i h₂;
          suffices proofset 𝓢 (□h₂.choose) = proofset 𝓢 (□(∼φ)) by rw [this] at h; simpa;
          apply proofset.eq_boxed_of_eq;
          rw [←h₂.choose_spec, hφ];
          simp;
        . exfalso;
          rename_i h₂;
          push_neg at h₂;
          apply @h₂ (∼φ);
          simpa;
      . intro h;
        split;
        . rename_i h₂;
          suffices proofset 𝓢 (□h₂.choose) = proofset 𝓢 (□(∼φ)) by rw [←this] at h; simpa;
          apply proofset.eq_boxed_of_eq;
          rw [←h₂.choose_spec, hφ];
          simp;
        . tauto;
-/

end minimalCanonicalFrame


end Neighborhood

end

end LO.Modal
