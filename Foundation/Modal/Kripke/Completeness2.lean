import Foundation.Modal.SaturatedConsistentTableau
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Entailment
open Formula
open Kripke
open SaturatedConsistentTableau

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

namespace Kripke


section

abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Kripke.Frame where
  World := SaturatedConsistentTableau 𝓢
  Rel t₁ t₂ := □''⁻¹t₁.1.1 ⊆ t₂.1.1

abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Model where
  toFrame := canonicalFrame 𝓢
  Val t a := (atom a) ∈ t.1.1

@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel 𝓢).World := Formula.Kripke.Satisfies.semantics (M := canonicalModel 𝓢)

end


namespace canonicalFrame

variable {t₁ t₂ : (canonicalFrame 𝓢).World}

@[simp] lemma rel_def_box: t₁ ≺ t₂ ↔ ∀ {φ}, □φ ∈ t₁.1.1 → φ ∈ t₂.1.1 := by simp [Frame.Rel']; aesop;

lemma multirel_def_multibox : t₁ ≺^[n] t₂ ↔ ∀ {φ}, □^[n]φ ∈ t₁.1.1 → φ ∈ t₂.1.1 := by
  induction n generalizing t₁ t₂ with
  | zero =>
    simp_all only [Rel.iterate.iff_zero, Function.iterate_zero, id_eq];
    constructor;
    . intro h; tauto_set;
    . intro h;
      apply equality_of₁;
      sorry;
      -- apply equality_of₁;
      -- tauto_set;
  | succ n ih =>
    constructor;
    . intro h φ hp;
      obtain ⟨⟨t₃, _⟩, R₁₃, R₃₂⟩ := h;
      apply ih.mp R₃₂ $ rel_def_box.mp R₁₃ (by simpa using hp);
    . intro h;
      obtain ⟨t, ht⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹{ φ | t₁ ⊧ φ }, □''^[n]{ ψ | ¬t₂ ⊧ ψ }⟩) $ by
        sorry;
      use t;
      constructor;
      . intro φ hφ;
        apply ht.1;
        intro t₃ ht₁₃;
        sorry;
      . apply ih.mpr;
        intro φ hφ;
        sorry;

lemma multirel_def_multibox' : t₁ ≺^[n] t₂ ↔ ∀ {φ}, φ ∈ (□''⁻¹^[n]t₁.1.1) → φ ∈ t₂.1.1 := by
  constructor;
  . intro h φ hp;
    exact multirel_def_multibox.mp h hp;
  . intro h;
    apply multirel_def_multibox.mpr;
    assumption;

lemma multirel_def_multidia : t₁ ≺^[n] t₂ ↔ ∀ {φ}, (φ ∈ t₂.1.1 → ◇^[n]φ ∈ t₁.1.1):= by
  sorry;

lemma rel_def_dia : t₁ ≺ t₂ ↔ ∀ {φ}, φ ∈ t₂.1.1 → ◇φ ∈ t₁.1.1 := by
  convert multirel_def_multidia (n := 1);
  simp;
  tauto;

end canonicalFrame



section lemmata

variable {φ ψ : Formula ℕ}

lemma truthlemma : ∀ {t : (canonicalModel 𝓢).World}, ((φ ∈ t.1.1) → t ⊧ φ) ∧ ((φ ∈ t.1.2) → ¬t ⊧ φ) := by
  induction φ using Formula.rec' with
  | hatom =>
    simp_all only [Semantics.Realize, Satisfies, implies_true, true_and];
    intro t h₁;
    exact iff_not_mem₁_mem₂.mpr h₁;
  | hfalsum =>
    simp [Semantics.Realize, Satisfies, false_iff];
  | himp φ ψ ihφ ihψ =>
    intro t;
    constructor;
    . intro h _;
      rcases of_mem₁_imp h with (hφ | hψ);
      . have := ihφ.2 hφ;
        contradiction;
      . exact ihψ.1 hψ;
    . intro h;
      replace h := of_mem₂_imp h;
      apply Satisfies.imp_def₂.not.mpr;
      push_neg;
      constructor;
      . apply ihφ.1; exact h.1;
      . apply ihψ.2; exact h.2;
  | hbox φ ihφ =>
    intro t;
    constructor;
    . intro h t' Rtt';
      apply ihφ.1;
      apply of_box_mem₁ h Rtt';
    . intro h;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      obtain ⟨t', Rtt', ht'⟩ := of_box_mem₂ h;
      use t';
      constructor;
      . exact Rtt';
      . apply ihφ.2 ht';

lemma iff_valid_on_canonicalModel_deducible : (canonicalModel 𝓢) ⊧ φ ↔ 𝓢 ⊢! φ := by
  constructor;
  . contrapose;
    intro h;
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      apply Tableau.iff_consistent_empty_singleton₂ (𝓢 := 𝓢) (φ := φ) |>.mpr;
      exact h;
    obtain ⟨t, ht⟩ := lindenbaum this;
    apply ValidOnModel.not_of_exists_world;
    use t;
    apply truthlemma.2;
    apply ht.2;
    tauto_set;
  . intro h t;
    suffices φ ∈ t.1.1 by exact truthlemma.1 this;
    exact SaturatedConsistentTableau.mem₁_of_provable h;

end lemmata


class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C

instance [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  contrapose;
  intro h;
  apply ValidOnFrameClass.not_of_exists_model;
  use (canonicalModel 𝓢);
  constructor;
  . exact Canonical.canonical;
  . exact iff_valid_on_canonicalModel_deducible.not.mpr h;
⟩

end Kripke

end LO.Modal
