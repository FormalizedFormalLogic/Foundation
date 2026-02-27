module

public import Foundation.Modal.Tableau
public import Foundation.Modal.Kripke2.Basic

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open MaximalConsistentTableau
open KripkeModel

variable [DecidableEq α] [Encodable α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]
variable {φ ψ : Formula α}

@[grind]
def canonicalKripkeModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : KripkeModel (MaximalConsistentTableau 𝓢) α where
  frame t₁ t₂ := □⁻¹'t₁.1.1 ⊆ t₂.1.1
  val a t := (atom a) ∈ t.1.1

attribute [grind .]
  MaximalConsistentTableau.not_mem₁_falsum
  MaximalConsistentTableau.mem₂_falsum
attribute [grind =] MaximalConsistentTableau.iff_mem₁_imp
attribute [grind =] MaximalConsistentTableau.iff_not_mem₁_mem₂
attribute [grind =]
  MaximalConsistentTableau.iff_mem₁_box
  MaximalConsistentTableau.iff_mem₂_box

namespace canonicalKripkeModel

variable {t : (canonicalKripkeModel 𝓢).world}

lemma truthlemma : (φ ∈ t.1.1 ↔ t ⊩ φ) ∧ (φ ∈ t.1.2 ↔ t ⊮ φ) := by
  induction φ generalizing t with
  | hatom | hfalsum | himp => grind;
  | hbox φ ihφ =>
    constructor;
    . constructor;
      . intro h t' Rtt';
        apply ihφ.1.1;
        grind;
      . intro h;
        apply iff_mem₁_box.mpr;
        intro t' Rtt';
        apply ihφ.1.2;
        exact h t' Rtt';
    . constructor;
      . intro h;
        apply forces_box.not.mpr;
        push_neg;
        obtain ⟨t', Rtt', ht'⟩ := iff_mem₂_box.mp h;
        use t';
        grind;
      . intro h;
        apply iff_mem₂_box.mpr;
        replace h := forces_box.not.mp h;
        grind;

@[grind =] lemma truthlemma₁ : φ ∈ t.1.1 ↔ t ⊩ φ := truthlemma.1
@[grind =] lemma truthlemma₂ : φ ∈ t.1.2 ↔ t ⊮ φ := truthlemma.2

@[grind =]
lemma iff_valid_provable : (canonicalKripkeModel 𝓢) ⊧ φ ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose!;
    intro h;
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      apply Tableau.iff_consistent_empty_singleton₂.mpr;
      exact h;
    obtain ⟨t, ht⟩ := lindenbaum this;
    apply notModels_of_exists_world_notForces;
    use t;
    apply truthlemma₂.mp;
    apply ht.2;
    tauto_set;
  . intro h t;
    exact truthlemma₁.mp $ MaximalConsistentTableau.iff_provable_mem₁.mp h t;


variable {x y : (canonicalKripkeModel 𝓢).world} {n : ℕ}

lemma iff_rel_forces_box : x ≺ y ↔ ∀ {φ}, x ⊩ □φ → y ⊩ φ := by grind;
lemma iff_relItr_forces_boxItr : x ≺^[n] y ↔ ∀ {φ}, x ⊩ □^[n]φ → y ⊩ φ := by
  constructor;
  . grind;
  . induction n generalizing x y with
    | zero =>
      suffices (∀ {φ : Formula _}, x ⊩ φ → y ⊩ φ) → x = y by simpa;
      intro h;
      apply intro_equality;
      . grind;
      . intro φ hφ;
        rw [truthlemma₂] at hφ ⊢;
        apply h (φ := ∼φ) (by grind);
    | succ n ih =>
      intro h;
      obtain ⟨t, ht⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨{ φ | x ⊩ □φ }, □^[n]'{ φ | y ⊮ φ }⟩) $ by
        intro Γ Δ hΓ hΔ;
        by_contra! hC;
        have : 𝓢 ⊢ □Γ.conj ➝ □Δ.disj := imply_box_distribute'! hC;
        have : □Δ.disj ∈ x.1.1 := mdp_mem₁_provable this $ by
          apply truthlemma₁.mpr;
          intro y Rxy;
          apply forces_fconj.mpr;
          intro φ hφ;
          apply hΓ hφ y Rxy;
        have : x ⊩ □Δ.disj := truthlemma₁.mp this;
        have : x ⊩ □^[(n + 1)](□⁻¹^[n]'Δ).disj := by
          suffices x ⊩ □□^[n](□⁻¹^[n]'Δ).disj by simpa;
          intro y Rxy;
          apply forces_boxItr.mpr;
          intro z Ryz;
          apply forces_fdisj.mpr;
          obtain ⟨ψ, hψ₁, hψ₂⟩ := forces_fdisj.mp $ this y Rxy;
          obtain ⟨ξ, hξ, rfl⟩ := hΔ hψ₁;
          use ξ;
          constructor;
          . simpa [Finset.LO.preboxItr];
          . exact forces_boxItr.mp hψ₂ _ Ryz;
        have : y ⊩ (□⁻¹^[n]'Δ).disj := h this;
        obtain ⟨ψ, hψ₁, hψ₂⟩ := forces_fdisj.mp $ this;
        have : y ⊮ ψ := Set.LO.mem_of_mem_boxItr $ @hΔ (□^[n]ψ) $ by
          show □^[n]ψ ∈ ↑Δ;
          grind;
        contradiction;
      use t;
      constructor;
      . intro φ hφ;
        apply ht.1;
        exact truthlemma₁.mp hφ;
      . apply ih;
        intro φ hφ;
        have := Set.compl_subset_compl.mpr ht.2 $ iff_not_mem₂_mem₁.mpr $ truthlemma₁.mpr hφ;
        grind;

lemma iff_relItr_boxItr_subset₁ : x ≺^[n] y ↔ ((□⁻¹^[n]'x.1.1) ⊆ y.1.1) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ iff_relItr_forces_boxItr.mp h $ truthlemma₁.mp hφ,
  fun h => iff_relItr_forces_boxItr.mpr fun hφ => truthlemma₁.mp (h $ truthlemma₁.mpr hφ)
⟩
lemma iff_rel_box_subset₁ : x ≺ y ↔ □⁻¹'x.1.1 ⊆ y.1.1 := by
  simpa using iff_relItr_boxItr_subset₁ (n := 1);


lemma iff_relItr_boxItr_subset₂ : x ≺^[n] y ↔ (y.1.2 ⊆ (□⁻¹^[n]'x.1.2)) := by
  apply Iff.trans iff_relItr_boxItr_subset₁;
  grind;
lemma iff_rel_box_subset₂ : x ≺ y ↔ (y.1.2 ⊆ (□⁻¹'x.1.2)) := by
  simpa using iff_relItr_boxItr_subset₂ (n := 1);

lemma iff_relItr_forces_diaItr : x ≺^[n] y ↔ ∀ {φ}, y ⊩ φ → x ⊩ (◇^[n]φ) := by
  constructor;
  . intro Rxy φ hφ;
    apply forces_diaItr.mpr;
    use y;
  . intro h;
    apply iff_relItr_forces_boxItr.mpr;
    intro φ;
    contrapose!;
    intro hφ;
    obtain ⟨z, Rxz, hz⟩ := forces_diaItr.mp $ h (φ := ∼φ) (by grind);
    grind;
lemma iff_rel_forces_dia : x ≺ y ↔ ∀ {φ}, y ⊩ φ → x ⊩ (◇φ) := by
  simpa using iff_relItr_forces_diaItr (n := 1);


lemma iff_relItr_diaItr_subset₁ : x ≺^[n] y ↔ (y.1.1 ⊆ (◇⁻¹^[n]'x.1.1)) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ iff_relItr_forces_diaItr.mp h $ truthlemma₁.mp hφ,
  fun h => iff_relItr_forces_diaItr.mpr fun hφ => truthlemma₁.mp $ h $ truthlemma₁.mpr hφ
⟩
lemma iff_rel_dia_subset₁ : x ≺ y ↔ (y.1.1 ⊆ (◇'⁻¹x.1.1)) := by
  simpa using iff_relItr_diaItr_subset₁ (n := 1);


lemma iff_relItr_diaItr_subset₂ : x ≺^[n] y ↔ ((◇⁻¹^[n]'x.1.2) ⊆ y.1.2) := by
  constructor;
  . intro Rxy φ;
    contrapose;
    intro hφ;
    apply iff_not_mem₂_mem₁.mpr;
    apply iff_relItr_diaItr_subset₁.mp Rxy;
    exact iff_not_mem₂_mem₁.mp hφ;
  . intro H;
    apply iff_relItr_diaItr_subset₁.mpr;
    intro φ;
    contrapose;
    intro hφ;
    exact iff_not_mem₁_mem₂.mpr $ @H φ (iff_not_mem₁_mem₂.mp hφ);
lemma iff_rel_dia_subset₂ : x ≺ y ↔ ((◇'⁻¹x.1.2) ⊆ y.1.2) := by
  simpa using iff_relItr_diaItr_subset₂ (n := 1);

end canonicalKripkeModel

end LO.Modal

end
