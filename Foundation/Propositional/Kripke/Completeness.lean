import Foundation.Propositional.Kripke.Basic
import Foundation.Propositional.ConsistentTableau

namespace LO.Propositional

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]
variable {t t₁ t₂ : SaturatedConsistentTableau 𝓢} {φ ψ : Formula ℕ}

open Entailment Entailment.FiniteContext
open Formula (atom)
open Formula.Kripke (Satisfies ValidOnModel)
open Kripke
open SaturatedConsistentTableau

namespace Kripke

def canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Int 𝓢] : Kripke.Frame where
  World := SaturatedConsistentTableau 𝓢
  Rel t₁ t₂ := t₁.1.1 ⊆ t₂.1.1
  rel_partial_order := {
    refl := by tauto_set
    trans := by tauto_set
    antisymm := fun x y Sxy Syx => equality_of₁ $ by tauto_set
  }

namespace canonicalFrame

variable {x y : canonicalFrame 𝓢}

lemma rel₁ : x ≺ y ↔ x.1.1 ⊆ y.1.1 := by simp [Frame.Rel', canonicalFrame]

lemma rel₂ : x ≺ y ↔ y.1.2 ⊆ x.1.2 := by
  constructor
  . intro h φ
    contrapose
    intro hφ
    apply iff_not_mem₂_mem₁.mpr
    apply h
    exact iff_not_mem₂_mem₁.mp hφ
  . intro h φ
    contrapose
    intro hφ
    apply iff_not_mem₁_mem₂.mpr
    apply h
    exact iff_not_mem₁_mem₂.mp hφ

end canonicalFrame


def canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Int 𝓢] : Kripke.Model where
  toFrame := Kripke.canonicalFrame 𝓢
  Val := ⟨λ t a => (atom a) ∈ t.1.1, by aesop⟩

namespace canonicalModel

variable [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

end canonicalModel


variable {C : Kripke.FrameClass}

section truthlemma

variable {t : (Kripke.canonicalModel 𝓢).World}

private lemma truthlemma.himp
  (ihp : ∀ {t : (Kripke.canonicalModel 𝓢).World}, t ⊧ φ ↔ φ ∈ t.1.1)
  (ihq : ∀ {t : (Kripke.canonicalModel 𝓢).World}, t ⊧ ψ ↔ ψ ∈ t.1.1)
  : t ⊧ φ ➝ ψ ↔ φ ➝ ψ ∈ t.1.1 := by
  constructor
  . contrapose
    intro h
    replace h := iff_not_mem₁_mem₂.mp h
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := (insert φ t.1.1, {ψ})) $ by
      intro Γ Δ hΓ hΔ
      by_contra hC
      apply t.consistent (Γ := Γ.erase φ) (Δ := {φ ➝ ψ}) ?_ ?_
      . simp only [Finset.disj_singleton]
        apply FConj_DT.mpr
        apply Context.deduct!
        replace hC := Context.weakening! (Δ := insert φ Γ.toSet) (by simp) $ FConj_DT.mp hC
        rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ)
        . simp only [Finset.coe_eq_empty] at hΔ
          subst hΔ
          simp only [Finset.disj_empty, Finset.coe_erase, Set.insert_diff_singleton] at hC ⊢
          exact of_O! hC
        . simp only [Finset.coe_eq_singleton] at hΔ
          subst hΔ
          simpa using hC
      . simpa using Set.iff_subset_insert_subset_diff.mp hΓ
      . simpa
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h
    apply Satisfies.imp_def.not.mpr
    push_neg
    use t'
    constructor
    . assumption
    . constructor
      . apply ihp.mpr
        assumption
      . apply ihq.not.mpr
        apply iff_not_mem₁_mem₂.mpr
        simp_all only [Set.singleton_subset_iff]
  . intro h t' htt' hp
    replace hp := ihp.mp hp
    have hpq := htt' h
    apply ihq.mpr
    apply iff_not_mem₂_mem₁.mp
    apply not_mem₂ (Γ := {φ, φ ➝ ψ})
    . simp only [Finset.coe_insert, Finset.coe_singleton]
      apply Set.doubleton_subset.mpr
      tauto
    . suffices 𝓢 ⊢! Finset.conj {φ, φ ➝ ψ} ➝ Finset.disj {ψ} by simpa
      apply CFConj_CDisj!_of_innerMDP (φ := φ) (ψ := ψ) <;> simp

lemma truthlemma : t ⊧ φ ↔ φ ∈ t.1.1 := by
  induction φ generalizing t with
  | hatom => tauto
  | hfalsum => simp only [Semantics.Bot.realize_bot, not_mem₁_falsum]
  | himp φ ψ ihp ihq => exact truthlemma.himp ihp ihq
  | hand φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_and, *]
  | hor φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_or, *]

lemma iff_valid_on_canonicalModel_deducible : (Kripke.canonicalModel 𝓢) ⊧ φ ↔ 𝓢 ⊢! φ := by
  constructor
  . contrapose
    intro h
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      simp only [Tableau.Consistent]
      rintro Γ Δ hΓ hΔ
      by_contra hC
      apply h
      rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ)
      . simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ
        subst hΓ hΔ
        simp only [Finset.conj_empty, Finset.disj_empty] at hC
        exact of_O! $ hC ⨀ verum!
      . simp only [Set.subset_empty_iff, Finset.coe_eq_empty, Finset.coe_eq_singleton] at hΓ hΔ
        subst hΓ hΔ
        simp only [Finset.conj_empty, Finset.disj_singleton] at hC
        exact hC ⨀ verum!
    obtain ⟨t', ht'⟩ := lindenbaum this
    simp only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, not_forall]
    existsi t'
    apply truthlemma.not.mpr
    apply iff_not_mem₁_mem₂.mpr
    simp_all
  . intro h t
    suffices φ ∈ t.1.1 by exact truthlemma.mpr this
    exact mem₁_of_provable h

end truthlemma


class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Int 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C

instance instCompleteOfCanonical [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  intro φ h
  apply iff_valid_on_canonicalModel_deducible.mp
  apply h
  exact Canonical.canonical
⟩

end Kripke

end LO.Propositional
