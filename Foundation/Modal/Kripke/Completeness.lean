import Foundation.Modal.Tableau
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Entailment
open Formula
open Kripke
open MaximalConsistentTableau

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

namespace Kripke


section

abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Kripke.Frame where
  World := MaximalConsistentTableau 𝓢
  Rel t₁ t₂ := □'⁻¹t₁.1.1 ⊆ t₂.1.1

abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Model where
  toFrame := canonicalFrame 𝓢
  Val t a := (atom a) ∈ t.1.1

@[reducible]
instance : Semantics (canonicalModel 𝓢) (Formula ℕ) := Formula.Kripke.Satisfies.semantics (M := canonicalModel 𝓢)

end


section lemmata

variable {φ ψ : Formula ℕ}
variable {t : (canonicalModel 𝓢).World}

lemma truthlemma : ((φ ∈ t.1.1) ↔ t ⊧ φ) ∧ ((φ ∈ t.1.2) ↔ ¬t ⊧ φ) := by
  induction φ generalizing t with
  | hatom =>
    simp_all only [Semantics.Models, Satisfies, true_and];
    exact iff_not_mem₁_mem₂.symm;
  | hfalsum => simp [Semantics.Models, Satisfies];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . constructor;
      . intro hφψ hφ;
        rcases iff_mem₁_imp.mp hφψ with (hφ | hψ);
        . have := ihφ.2.1 hφ; contradiction;
        . exact ihψ.1.1 hψ;
      . intro hφψ;
        rcases Satisfies.imp_def₂.mp hφψ with (hφ | hψ);
        . apply iff_mem₁_imp.mpr;
          left;
          exact ihφ.2.2 hφ;
        . apply iff_mem₁_imp.mpr;
          right;
          exact ihψ.1.2 hψ;
    . constructor;
      . intro hφψ;
        rcases iff_mem₂_imp.mp hφψ with ⟨hφ, hψ⟩;
        apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . exact ihφ.1.mp hφ;
        . exact ihψ.2.mp hψ;
      . intro hφψ;
        apply iff_mem₂_imp.mpr;
        replace hφψ := Satisfies.imp_def₂.not.mp hφψ;
        push_neg at hφψ;
        rcases hφψ with ⟨hφ, hψ⟩;
        constructor;
        . exact ihφ.1.mpr hφ;
        . exact ihψ.2.mpr hψ;
  | hbox φ ihφ =>
    constructor;
    . constructor;
      . intro h t' Rtt';
        apply ihφ.1.1;
        exact iff_mem₁_box.mp h Rtt';
      . intro h;
        apply iff_mem₁_box.mpr;
        intro t' Rtt';
        apply ihφ.1.2;
        exact h t' Rtt';
    . constructor;
      . intro h;
        apply Satisfies.box_def.not.mpr;
        push_neg;
        obtain ⟨t', Rtt', ht'⟩ := iff_mem₂_box.mp h;
        use t';
        constructor;
        . exact Rtt';
        . exact ihφ.2.mp ht';
      . intro h;
        apply iff_mem₂_box.mpr;
        replace h := Satisfies.box_def.not.mp h;
        push_neg at h;
        obtain ⟨t', Rtt', ht'⟩ := h;
        use t';
        constructor;
        . exact Rtt';
        . exact ihφ.2.mpr ht';

lemma truthlemma₁ : (φ ∈ t.1.1) ↔ t ⊧ φ := truthlemma.1

lemma truthlemma₂ : (φ ∈ t.1.2) ↔ ¬t ⊧ φ := truthlemma.2

lemma iff_valid_on_canonicalModel_deducible : (canonicalModel 𝓢) ⊧ φ ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose;
    intro h;
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      apply Tableau.iff_consistent_empty_singleton₂ (𝓢 := 𝓢) (φ := φ) |>.mpr;
      exact h;
    obtain ⟨t, ht⟩ := lindenbaum this;
    apply ValidOnModel.not_of_exists_world;
    use t;
    apply truthlemma₂.mp;
    apply ht.2;
    tauto_set;
  . intro h t;
    exact truthlemma₁.mp $ MaximalConsistentTableau.iff_provable_mem₁.mp h t;

end lemmata


class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C

instance [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  contrapose;
  intro h;
  apply not_validOnFrameClass_of_exists_model;
  use (canonicalModel 𝓢);
  constructor;
  . exact Canonical.canonical;
  . exact iff_valid_on_canonicalModel_deducible.not.mpr h;
⟩


namespace canonicalModel

open Formula.Kripke.Satisfies

variable {x y : (canonicalModel 𝓢).World}

lemma def_rel_box_mem₁ : x ≺ y ↔ □'⁻¹x.1.1 ⊆ y.1.1 := by simp [Frame.Rel'];

lemma def_rel_box_satisfies : x ≺ y ↔ ∀ {φ}, x ⊧ □φ → y ⊧ φ := by
  constructor;
  . intro h φ hφ;
    exact truthlemma₁.mp $  def_rel_box_mem₁.mp h (truthlemma₁.mpr hφ);
  . intro h;
    apply def_rel_box_mem₁.mpr;
    intro φ hφ;
    exact truthlemma₁.mpr $ h $ truthlemma₁.mp hφ

lemma def_multirel_boxItr_satisfies : x ≺^[n] y ↔ (∀ {φ}, x ⊧ □^[n]φ → y ⊧ φ) := by
  constructor;
  . intro h φ hφ;
    exact Satisfies.boxItr_def.mp hφ h;
  . induction n generalizing x y with
    | zero =>
      suffices (∀ {φ : Formula ℕ}, x ⊧ φ → y ⊧ φ) → x = y by simpa;
      intro h;
      apply intro_equality;
      . intro φ hφ; exact truthlemma₁.mpr $ h $ truthlemma₁.mp hφ;
      . intro φ hφ; exact truthlemma₂.mpr $ h $ Satisfies.not_def.mpr $ truthlemma₂.mp hφ;
    | succ n ih =>
      intro h;
      obtain ⟨t, ht⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨{ φ | x ⊧ □φ }, □'^[n]{ φ | ¬y ⊧ φ }⟩) $ by
        intro Γ Δ hΓ hΔ;
        by_contra! hC;
        have : 𝓢 ⊢ □Γ.conj ➝ □Δ.disj := imply_box_distribute'! hC;
        have : □Δ.disj ∈ x.1.1 := mdp_mem₁_provable this $ by
          apply truthlemma₁.mpr;
          intro y Rxy;
          apply Satisfies.fconj_def.mpr;
          intro φ hφ;
          apply hΓ hφ y Rxy;
        have : x ⊧ □Δ.disj := truthlemma₁.mp this;
        have : x ⊧ □^[(n + 1)](□'⁻¹^[n]Δ).disj := by
          suffices x ⊧ □□^[n](□'⁻¹^[n]Δ).disj by simpa;
          intro y Rxy;
          apply boxItr_def.mpr;
          intro z Ryz;
          obtain ⟨ψ, hψ₁, hψ₂⟩ := Satisfies.fdisj_def.mp $ this y Rxy;
          obtain ⟨ξ, _, rfl⟩ := by simpa using hΔ hψ₁;
          apply Satisfies.fdisj_def.mpr;
          use ξ;
          constructor;
          . simpa;
          . exact Satisfies.boxItr_def.mp hψ₂ Ryz;
        have : y ⊧ (□'⁻¹^[n]Δ).disj := h this;
        obtain ⟨ψ, hψ₁, hψ₂⟩ := fdisj_def.mp this;
        have : ¬y ⊧ ψ := by simpa using @hΔ (□^[n]ψ) (by simpa using hψ₁);
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

lemma def_multirel_boxItr_mem₁ : x ≺^[n] y ↔ ((□'⁻¹^[n]x.1.1) ⊆ y.1.1) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ def_multirel_boxItr_satisfies.mp h $ truthlemma₁.mp hφ,
  fun h => def_multirel_boxItr_satisfies.mpr fun hφ => truthlemma₁.mp (h $ truthlemma₁.mpr hφ)
⟩

lemma def_multirel_boxItr_mem₂ : x ≺^[n] y ↔ (y.1.2 ⊆ (□'⁻¹^[n]x.1.2)) := by
  apply Iff.trans def_multirel_boxItr_mem₁;
  constructor;
  . intro h φ;
    contrapose!;
    intro hφ;
    apply iff_not_mem₂_mem₁.mpr;
    apply h;
    apply iff_not_mem₂_mem₁.mp;
    assumption;
  . intro h φ;
    contrapose!;
    intro hφ;
    apply iff_not_mem₁_mem₂.mpr;
    apply h;
    apply iff_not_mem₁_mem₂.mp;
    assumption;

lemma def_rel_box_mem₂ : x ≺ y ↔ (y.1.2 ⊆ (□'⁻¹ x.1.2)) := by
  simpa using def_multirel_boxItr_mem₂ (n := 1);

lemma def_multirel_diaItr_satisfies : x ≺^[n] y ↔ (∀ {φ}, y ⊧ φ → x ⊧ ◇^[n]φ) := by
  constructor;
  . intro h φ hφ;
    apply Formula.Kripke.Satisfies.diaItr_def.mpr;
    use y;
  . intro h;
    apply def_multirel_boxItr_satisfies.mpr;
    intro φ;
    contrapose;
    intro hφ;
    apply Satisfies.not_def.mp;
    have : x ⊧ ∼□^[n](∼∼φ) := diaItr_dual.mp $ h (φ := ∼φ) (Satisfies.not_def.mp hφ);
    revert this;
    apply intro_neg_semiequiv;
    apply intro_boxItr_semiequiv;
    intro _ _;
    apply negneg_def.mpr;

lemma def_multirel_diaItr_mem₁ : x ≺^[n] y ↔ (y.1.1 ⊆ (□'⁻¹^[n]x.1.1)) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ def_multirel_diaItr_satisfies.mp h (truthlemma₁.mp hφ),
  fun h => def_multirel_diaItr_satisfies.mpr fun hφ => truthlemma₁.mp $ h (truthlemma₁.mpr hφ)
⟩

lemma def_rel_dia_mem₁ : x ≺ y ↔ (y.1.1 ⊆ (□'⁻¹ x.1.1)) := by
  simpa using def_multirel_diaItr_mem₁ (n := 1);

lemma def_multirel_diaItr_mem₂ : x ≺^[n] y ↔ ((◇'⁻¹^[n]x.1.2) ⊆ y.1.2) := by
  constructor;
  . intro Rxy φ;
    contrapose;
    intro hφ;
    apply iff_not_mem₂_mem₁.mpr;
    apply def_multirel_diaItr_mem₁.mp Rxy;
    exact iff_not_mem₂_mem₁.mp hφ;
  . intro H;
    apply def_multirel_diaItr_mem₁.mpr;
    intro φ;
    contrapose;
    intro hφ;
    exact iff_not_mem₁_mem₂.mpr $ @H φ (iff_not_mem₁_mem₂.mp hφ);

lemma def_rel_dia_mem₂ : x ≺ y ↔ ((◇'⁻¹x.1.2) ⊆ y.1.2) := by
  simpa using def_multirel_diaItr_mem₂ (n := 1);

end canonicalModel

end Kripke

end LO.Modal
