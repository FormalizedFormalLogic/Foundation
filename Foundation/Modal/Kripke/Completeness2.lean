import Foundation.Modal.Tableau
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Entailment
open Formula
open Kripke
open MaximalConsistentTableau

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

namespace Kripke


section

abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Kripke.Frame where
  World := MaximalConsistentTableau 𝓢
  Rel t₁ t₂ := □''⁻¹t₁.1.1 ⊆ t₂.1.1

abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Model where
  toFrame := canonicalFrame 𝓢
  Val t a := (atom a) ∈ t.1.1

@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel 𝓢).World := Formula.Kripke.Satisfies.semantics (M := canonicalModel 𝓢)

end


section lemmata

variable {φ ψ : Formula ℕ}
variable {t : (canonicalModel 𝓢).World}

lemma truthlemmaAux : ∀ {t : (canonicalModel 𝓢).World}, ((φ ∈ t.1.1) → t ⊧ φ) ∧ ((φ ∈ t.1.2) → ¬t ⊧ φ) := by
  induction φ using Formula.rec' with
  | hatom =>
    simp_all only [Semantics.Realize, Satisfies, implies_true, true_and];
    intro t h₁;
    exact iff_not_mem₁_mem₂.mpr h₁;
  | hfalsum => simp [Semantics.Realize, Satisfies];
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
      apply MaximalConsistentTableau.of_mem₁_box h Rtt';
    . intro h;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      obtain ⟨t', Rtt', ht'⟩ := MaximalConsistentTableau.of_mem₂_box h;
      use t';
      constructor;
      . exact Rtt';
      . apply ihφ.2 ht';

lemma truthlemmaAux₁ : (φ ∈ t.1.1) → t ⊧ φ := truthlemmaAux (t := t) |>.1

lemma truthlemmaAux₂ : (φ ∈ t.1.2) → ¬t ⊧ φ := truthlemmaAux (t := t) |>.2

lemma truthlemma₁ : (φ ∈ t.1.1) ↔ t ⊧ φ := by
  constructor;
  . apply truthlemmaAux₁;
  . intro h;
    induction φ using Formula.rec' with
    | hatom => simpa [Semantics.Realize, Satisfies] using h;
    | hfalsum => simpa;
    | himp φ ψ ihφ ihψ =>
      sorry;
    | hbox φ ih =>
      sorry;

lemma truthlemma₂ : (φ ∈ t.1.2) ↔ ¬t ⊧ φ := by
  constructor;
  . intro h;
    exact truthlemmaAux₂ h;
  . intro h;
    exact iff_not_mem₁_mem₂.mp $ truthlemma₁.not.mpr h;

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
  apply ValidOnFrameClass.not_of_exists_model;
  use (canonicalModel 𝓢);
  constructor;
  . exact Canonical.canonical;
  . exact iff_valid_on_canonicalModel_deducible.not.mpr h;
⟩


namespace canonicalModel

open Formula.Kripke.Satisfies

variable {x y : (canonicalModel 𝓢).World}

lemma def_rel_box : x ≺ y ↔ ∀ {φ}, □φ ∈ x.1.1 → φ ∈ y.1.1 := by simp [Frame.Rel']; aesop;

lemma def_multirel_multibox : x ≺^[n] y ↔ (∀ {φ}, x ⊧ □^[n]φ → y ⊧ φ) := by
  constructor;
  . intro h φ hφ;
    exact Satisfies.multibox_def.mp hφ h;
  . induction n generalizing x y with
    | zero =>
      simp_all only [Rel.iterate.iff_zero, Function.iterate_zero, id_eq];
      sorry;
    | succ n ih =>
      sorry;

lemma def_multirel_multibox_mem₁ : x ≺^[n] y ↔ (∀ {φ}, □^[n]φ ∈ x.1.1 → φ ∈ y.1.1) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ def_multirel_multibox.mp h $ truthlemma₁.mp hφ,
  fun h => def_multirel_multibox.mpr fun hφ => truthlemma₁.mp (h $ truthlemma₁.mpr hφ)
⟩

lemma def_multirel_multidia : x ≺^[n] y ↔ (∀ {φ}, y ⊧ φ → x ⊧ ◇^[n]φ) := by
  constructor;
  . intro h φ hφ;
    apply Formula.Kripke.Satisfies.multidia_def.mpr;
    use y;
  . intro h;
    apply def_multirel_multibox.mpr;
    intro φ;
    contrapose;
    intro hφ;
    have := h (φ := ∼φ) (Satisfies.not_def.mp hφ);
    sorry;

lemma def_multirel_multidia_mem₁ : x ≺^[n] y ↔ (∀ {φ}, φ ∈ y.1.1 → ◇^[n]φ ∈ x.1.1) := ⟨
  fun h _ hφ => truthlemma₁.mpr $ def_multirel_multidia.mp h (truthlemma₁.mp hφ),
  fun h => def_multirel_multidia.mpr fun hφ => truthlemma₁.mp $ h (truthlemma₁.mpr hφ)
⟩

lemma def_multirel_multidia_mem₂ : x ≺^[n] y ↔ (∀ {φ}, ◇^[n]φ ∈ x.1.2 → φ ∈ y.1.2) := by
  constructor;
  . intro Rxy φ;
    contrapose;
    intro hφ;
    apply iff_not_mem₂_mem₁.mpr;
    apply def_multirel_multidia_mem₁.mp Rxy;
    exact iff_not_mem₂_mem₁.mp hφ;
  . intro H;
    apply def_multirel_multidia_mem₁.mpr;
    intro φ;
    contrapose;
    intro hφ;
    exact iff_not_mem₁_mem₂.mpr $ @H φ (iff_not_mem₁_mem₂.mp hφ);

end canonicalModel

end Kripke

end LO.Modal
