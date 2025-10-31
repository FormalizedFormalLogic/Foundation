/-
  Maximal consistent set for basic modal logic
-/
import Foundation.Propositional.MCS
import Foundation.Modal.Entailment.K
import Foundation.Vorspiel.Set.Supplemental

namespace LO.MaximalConsistentSet

open Set.LO
open LO.Entailment LO.Entailment.Context
open LO.Modal LO.Modal.Entailment

variable {F} [DecidableEq F] [BasicModalLogicalConnective F]
         {S} [Entailment S F]
         {𝓢 : S} [Entailment.K 𝓢]

variable {Γ Γ₁ Γ₂ : MaximalConsistentSet 𝓢} {φ ψ : F} {n : ℕ}

lemma iff_mem_multibox : (□^[n]φ ∈ Γ) ↔ (∀ {Γ' : MaximalConsistentSet 𝓢}, (Γ.1.premultibox n ⊆ Γ'.1) → (φ ∈ Γ')) := by
  constructor;
  . intro hp Γ' hΓ'; apply hΓ'; simpa;
  . contrapose!;
    intro hp;
    obtain ⟨Γ', hΓ'⟩ := lindenbaum (𝓢 := 𝓢) (Γ := insert (∼φ) (Γ.1.premultibox n)) (by
      apply iff_consistent_insert_neg_unprovable.mpr;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : 𝓢 ⊢ □^[n]⋀Γ ➝ □^[n]φ := imply_multibox_distribute'! hΓ₂;
      have : 𝓢 ⊬ □^[n]⋀Γ ➝ □^[n]φ := by
        have := Context.provable_iff.not.mp $ iff_mem_provable.not.mp hp;
        push_neg at this;
        have : 𝓢 ⊬ ⋀(Γ.multibox n) ➝ □^[n]φ := FiniteContext.provable_iff.not.mp $ this (Γ.multibox n) (by
          intro ψ hq;
          obtain ⟨χ, hr₁, rfl⟩ := List.exists_multibox_of_mem_multibox hq;
          simpa using hΓ₁ χ hr₁;
        );
        revert this;
        contrapose;
        simp only [not_not];
        exact C!_trans collect_multibox_conj!;
      contradiction;
    );
    use Γ';
    constructor;
    . exact Set.Subset.trans (by tauto_set) hΓ';
    . apply iff_mem_neg.mp;
      apply hΓ';
      simp only [Set.mem_insert_iff, true_or]

lemma iff_mem_box : (□φ ∈ Γ) ↔ (∀ {Γ' : MaximalConsistentSet 𝓢}, (Γ.1.prebox ⊆ Γ'.1) → (φ ∈ Γ')) := iff_mem_multibox (n := 1)


lemma multibox_dn_iff : (□^[n](∼∼φ) ∈ Γ) ↔ (□^[n]φ ∈ Γ) := by
  simp only [iff_mem_multibox];
  grind;

lemma box_dn_iff : (□(∼∼φ) ∈ Γ) ↔ (□φ ∈ Γ) := multibox_dn_iff (n := 1)


lemma mem_multibox_dual : □^[n]φ ∈ Γ ↔ ∼(◇^[n](∼φ)) ∈ Γ := by
  simp only [iff_mem_provable];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_left multibox_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_right multibox_duality!);

lemma mem_box_dual : □φ ∈ Γ ↔ (∼(◇(∼φ)) ∈ Γ) := mem_multibox_dual (n := 1)

lemma mem_multidia_dual : ◇^[n]φ ∈ Γ ↔ ∼(□^[n](∼φ)) ∈ Γ := by
  simp only [iff_mem_provable];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_left multidia_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_right multidia_duality!);
lemma mem_dia_dual : ◇φ ∈ Γ ↔ (∼(□(∼φ)) ∈ Γ) := mem_multidia_dual (n := 1)

lemma iff_mem_multidia : (◇^[n]φ ∈ Γ) ↔ (∃ Γ' : MaximalConsistentSet 𝓢, (Γ.1.premultibox n ⊆ Γ'.1) ∧ (φ ∈ Γ'.1)) := by
  constructor;
  . intro h;
    have := mem_multidia_dual.mp h;
    have := iff_mem_neg.mp this;
    have := iff_mem_multibox.not.mp this;
    push_neg at this;
    obtain ⟨Γ', h₁, h₂⟩ := this;
    use Γ';
    constructor;
    . exact h₁;
    . exact iff_mem_negneg.mp $ iff_mem_neg.mpr h₂;
  . rintro ⟨Γ', h₁, h₂⟩;
    apply mem_multidia_dual.mpr;
    apply iff_mem_neg.mpr;
    apply iff_mem_multibox.not.mpr;
    push_neg;
    use Γ';
    constructor;
    . exact h₁;
    . exact iff_mem_neg.mp $ iff_mem_negneg.mpr h₂;

lemma iff_mem_dia : (◇φ ∈ Γ) ↔ (∃ Γ' : MaximalConsistentSet 𝓢, (Γ.1.prebox ⊆ Γ'.1) ∧ (φ ∈ Γ'.1)) := iff_mem_multidia (n := 1)


lemma multibox_multidia : (∀ {φ}, (□^[n]φ ∈ Γ₁.1 → φ ∈ Γ₂.1)) ↔ (∀ {φ}, (φ ∈ Γ₂.1 → ◇^[n]φ ∈ Γ₁.1)) := by
  constructor;
  . intro h φ;
    contrapose!;
    intro h₂;
    apply iff_mem_neg.mp;
    apply h;
    apply iff_mem_negneg.mp;
    apply (neg_congruence $ mem_multidia_dual).mp;
    exact iff_mem_neg.mpr h₂;
  . intro h φ;
    contrapose!;
    intro h₂;
    apply iff_mem_neg.mp;
    apply (neg_congruence $ mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply h;
    exact iff_mem_neg.mpr h₂;


end LO.MaximalConsistentSet
