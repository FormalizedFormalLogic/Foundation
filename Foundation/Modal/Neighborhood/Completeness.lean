import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Entailment.EM

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

section

open MaximalConsistentSet

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.Cl 𝓢]

abbrev Proofset (𝓢 : S) := Set (MaximalConsistentSet 𝓢)

def proofset (𝓢 : S) (φ : Formula α) : Proofset 𝓢 := { Γ : MaximalConsistentSet 𝓢 | φ ∈ Γ }

def Nonproofset (𝓢 : S) := { P : Proofset 𝓢 // ∀ φ, P ≠ proofset 𝓢 φ }

namespace proofset

local notation "‖" φ "‖" => proofset 𝓢 φ

variable {φ ψ : Formula α} {Γ : MaximalConsistentSet 𝓢}

omit [DecidableEq α] [Entailment.Cl 𝓢] in
@[grind]
lemma iff_mem : φ ∈ Γ ↔ Γ ∈ ‖φ‖ := by simp [proofset];

omit [DecidableEq α] [Entailment.Cl 𝓢] in
lemma mem_of_mem_of_subset (h : ‖φ‖ ⊆ ‖ψ‖) : φ ∈ Γ → ψ ∈ Γ := by
  intro hφ;
  grind;

omit [DecidableEq α] [Entailment.Cl 𝓢] in
@[grind] lemma iff_mem_of_eq (h : ‖φ‖ = ‖ψ‖) : φ ∈ Γ ↔ ψ ∈ Γ := by grind;

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
  suffices 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ □φ ➝ □ψ by simpa [imp_subset];
  apply Entailment.rm!;

end proofset

end


namespace Neighborhood

open Formula (atom)
open Formula.Neighborhood
open MaximalConsistentSet

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.E 𝓢] [Entailment.Consistent 𝓢]
variable {φ ψ ξ : Formula ℕ}


structure Canonicity (𝓢 : S) where
  𝒩 : MaximalConsistentSet 𝓢 → Set (Set (MaximalConsistentSet 𝓢))
  def_𝒩 : ∀ X : MaximalConsistentSet 𝓢, ∀ φ, □φ ∈ X ↔ proofset 𝓢 φ ∈ 𝒩 X
  V : ℕ → Set (MaximalConsistentSet 𝓢)
  def_V : ∀ a, V a = proofset 𝓢 (.atom a)

namespace Canonicity

attribute [simp, grind] def_𝒩 def_V

variable {𝓒 : Canonicity 𝓢}

def toModel (𝓒 : Canonicity 𝓢) : Model where
  World := MaximalConsistentSet 𝓢
  𝒩 := 𝓒.𝒩
  Val := 𝓒.V

@[simp]
lemma box_proofset : 𝓒.toModel.box (proofset 𝓢 φ) = (proofset 𝓢 (□φ)) := by
  ext w;
  apply Iff.trans ?_ (𝓒.def_𝒩 w φ).symm;
  simp [toModel];

@[simp]
lemma multibox_proofset : 𝓒.toModel.box^[n] (proofset 𝓢 φ) = (proofset 𝓢 (□^[n]φ)) := by
  induction n generalizing φ with
  | zero => simp;
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, box_proofset, ih];

@[simp]
lemma dia_proofset : 𝓒.toModel.dia (proofset 𝓢 φ) = (proofset 𝓢 (◇φ)) := by
  suffices 𝓒.toModel.dia (proofset 𝓢 φ) = (proofset 𝓢 (∼(□(∼φ)))) by tauto;
  simpa using 𝓒.box_proofset (φ := ∼φ);

@[simp]
lemma multidia_proofset : 𝓒.toModel.dia^[n] (proofset 𝓢 φ) = (proofset 𝓢 (◇^[n]φ)) := by
  induction n generalizing φ with
  | zero => simp;
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, dia_proofset, ih];

@[grind]
lemma iff_box {Γ : 𝓒.toModel} : □φ ∈ Γ.1 ↔ Γ ∈ 𝓒.toModel.box (proofset 𝓢 φ) := by apply 𝓒.def_𝒩

@[grind]
lemma iff_dia {Γ : 𝓒.toModel} : ◇φ ∈ Γ.1 ↔ Γ ∈ 𝓒.toModel.dia (proofset 𝓢 φ) := calc
  _ ↔ ∼□(∼φ) ∈ Γ.1 := by rfl;
  _ ↔ □(∼φ) ∉ Γ.1 := by apply MaximalConsistentSet.iff_mem_neg;
  _ ↔ (proofset 𝓢 (∼φ)) ∉ (𝓒.𝒩 Γ) := by simpa using iff_box (Γ := Γ) (φ := ∼φ) |>.not;
  _ ↔ _ := by simp [toModel];

@[grind]
lemma truthlemma : (proofset 𝓢 φ) = (𝓒.toModel φ) := by
  induction φ with
  | hatom => apply 𝓒.def_V _ |>.symm;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ => simp_all [proofset.eq_imp];
  | hbox φ ihφ =>
    suffices proofset 𝓢 (□φ) = 𝓒.toModel.box (𝓒.toModel.truthset φ) by simpa;
    rw [←ihφ, box_proofset];

lemma completeness {C : FrameClass} (hC : 𝓒.toModel.toFrame ∈ C) : LO.Complete 𝓢 C := by
  constructor;
  intro φ hφ;
  contrapose! hφ;
  obtain ⟨Γ, hΓ⟩ := lindenbaum $ FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hφ;
  apply not_validOnFrameClass_of_exists_model_world;
  use 𝓒.toModel, Γ;
  constructor;
  . assumption;
  . suffices Γ ∉ proofset 𝓢 φ by simpa [Semantics.Realize, Satisfies, 𝓒.truthlemma];
    apply proofset.iff_mem.not.mp;
    apply MaximalConsistentSet.iff_mem_neg.mp;
    tauto;

end Canonicity


def minimalCanonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 where
  𝒩 Γ X := ∃ φ, □φ ∈ Γ ∧ X = proofset 𝓢 φ
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      use φ;
    . rintro ⟨ψ, hψ₁, hψ₂⟩;
      have := proofset.eq_boxed_of_eq hψ₂;
      grind;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;


lemma minimalCanonicity.iff_mem_box_exists_fml {X} {Γ : (minimalCanonicity 𝓢).toModel}
  : Γ ∈ Frame.box _ X ↔ ∃ φ, X = proofset 𝓢 φ ∧ Frame.box _ X = proofset 𝓢 (□φ) ∧ Γ ∈ proofset 𝓢 (□φ)
  := by
    constructor;
    . rintro ⟨φ, _, rfl⟩;
      use φ;
      simpa;
    . tauto;

lemma minimalCanonicity.iff_mem_dia_forall_fml {X} {Γ : (minimalCanonicity 𝓢).toModel}
  : Γ ∈ Frame.dia _ X ↔ ∀ φ, Xᶜ ≠ proofset 𝓢 φ ∨ Frame.box _ Xᶜ ≠ proofset 𝓢 (□φ) ∨ Γ ∉ proofset 𝓢 (□φ)
  := by
    apply Iff.trans (iff_mem_box_exists_fml.not);
    set_option push_neg.use_distrib true in push_neg;
    rfl;

end Neighborhood


end LO.Modal
