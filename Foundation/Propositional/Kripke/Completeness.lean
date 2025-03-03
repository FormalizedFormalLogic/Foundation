import Foundation.Propositional.Kripke.Basic
import Foundation.Propositional.ConsistentTableau

namespace LO.Propositional

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]
variable {t t₁ t₂ : SaturatedConsistentTableau 𝓢} {φ ψ : Formula ℕ}

open Entailment Entailment.FiniteContext
open Formula (atom)
open Formula.Kripke (Satisfies ValidOnModel)
open Kripke
open SaturatedConsistentTableau

namespace Kripke

def canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢] : Kripke.Frame where
  World := SaturatedConsistentTableau 𝓢
  Rel t₁ t₂ := t₁.1.1 ⊆ t₂.1.1
  rel_refl := by tauto_set
  rel_trans := by tauto_set
    -- antisymm := fun x y Sxy Syx => equality_of₁ $ by tauto_set;

namespace canonicalFrame

variable [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]

end canonicalFrame


def canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢] : Kripke.Model where
  toFrame := Kripke.canonicalFrame 𝓢
  Val := ⟨λ t a => (atom a) ∈ t.1.1, by aesop⟩

namespace canonicalModel

variable [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]

end canonicalModel


variable {C : Kripke.FrameClass}

section truthlemma

variable {t : (Kripke.canonicalModel 𝓢).World}

private lemma truthlemma.himp
  (ihp : ∀ {t : (Kripke.canonicalModel 𝓢).World}, t ⊧ φ ↔ φ ∈ t.1.1)
  (ihq : ∀ {t : (Kripke.canonicalModel 𝓢).World}, t ⊧ ψ ↔ ψ ∈ t.1.1)
  : t ⊧ φ ➝ ψ ↔ φ ➝ ψ ∈ t.1.1 := by
  constructor;
  . contrapose;
    simp_all [Satisfies];
    intro h;
    replace h := iff_not_mem₁_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := (insert φ t.1.1, {ψ})) $ by
      simp only [Tableau.Consistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ χ, χ ∈ Γ.remove φ → χ ∈ t.1.1 := by
        intro χ hr;
        have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
        have := by simpa using hΓ χ hr₁;
        simp_all;
      by_contra hC;
      have : 𝓢 ⊢! ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj! hC) (by
        apply deduct'!;
        apply deduct!;
        have : [φ, φ ➝ ⋁Δ] ⊢[𝓢]! φ := by_axm!;
        have : [φ, φ ➝ ⋁Δ] ⊢[𝓢]! ⋁Δ := by_axm! ⨀ this;
        exact disj_allsame'! (by simpa using hΔ) this;
      )
      have : 𝓢 ⊬ ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := by simpa using (t.consistent hΓ (show ∀ χ ∈ [φ ➝ ψ], χ ∈ t.1.2 by simp_all));
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    use t';
    constructor;
    . assumption;
    . constructor;
      . assumption;
      . apply iff_not_mem₁_mem₂.mpr;
        simp_all only [Set.singleton_subset_iff];
  . simp [Satisfies.imp_def];
    intro h t' htt' hp;
    replace hp := ihp.mp hp;
    have hpq := htt' h;
    apply ihq.mpr;
    apply iff_not_mem₂_mem₁.mp;
    exact not_mem₂
      (by simp_all)
      (show 𝓢 ⊢! ⋀[φ, φ ➝ ψ] ➝ ψ by
        simp;
        apply and_imply_iff_imply_imply'!.mpr;
        apply deduct'!;
        apply deduct!;
        exact by_axm! ⨀ (by_axm! (φ := φ));
      );

lemma truthlemma : t ⊧ φ ↔ φ ∈ t.1.1 := by
  induction φ using Formula.rec' generalizing t with
  | hatom => tauto;
  | hfalsum => simp only [Semantics.Bot.realize_bot, not_mem₁_falsum];
  | himp φ ψ ihp ihq => exact truthlemma.himp ihp ihq;
  | hand φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_and, *];
  | hor φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_or, *];

lemma iff_valid_on_canonicalModel_deducible : (Kripke.canonicalModel 𝓢) ⊧ φ ↔ 𝓢 ⊢! φ := by
  constructor;
  . contrapose;
    intro h;
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      simp only [Tableau.Consistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
      subst hΓ;
      have : 𝓢 ⊢! φ := disj_allsame'! hΔ (hC ⨀ verum!);
      contradiction;
    obtain ⟨t', ht'⟩ := lindenbaum this;
    simp [ValidOnModel.iff_models, ValidOnModel]
    existsi t';
    apply truthlemma.not.mpr;
    apply iff_not_mem₁_mem₂.mpr;
    simp_all;
  . intro h t;
    suffices φ ∈ t.1.1 by exact truthlemma.mpr this;
    exact mem₁_of_provable h;

end truthlemma


class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C

instance instCompleteOfCanonical [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  intro φ h;
  apply iff_valid_on_canonicalModel_deducible.mp;
  apply h;
  exact Canonical.canonical;
⟩

end Kripke

end LO.Propositional
