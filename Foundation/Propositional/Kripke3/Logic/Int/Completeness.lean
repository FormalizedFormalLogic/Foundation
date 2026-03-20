module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Propositional.ConsistentTableau
public import Foundation.Propositional.Entailment.Minimal.Basic
public import Foundation.Propositional.Kripke.Basic
public import Foundation.Propositional.Hilbert.Standard.Basic

@[expose] public section

namespace LO.Propositional

variable [Encodable α] [DecidableEq α]

variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open LO.Entailment
open SaturatedConsistentTableau
open KripkeModel

def canonicalKripkeModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]
  : KripkeModel (SaturatedConsistentTableau 𝓢) α where
  frame t₁ t₂ := t₁.1.1 ⊆ t₂.1.1
  val a t := (#a) ∈ t.1.1

instance : KripkeModel.Intuitionistic (canonicalKripkeModel 𝓢) where
  refl := by tauto_set;
  trans := by tauto_set;
  atom_persistency := by tauto;

namespace canonicalKripkeModel

variable {x y t t₁ t₂ : (canonicalKripkeModel 𝓢).world} {φ ψ : Formula α}

lemma def_rel₁ : x ≺ y ↔ x.1.1 ⊆ y.1.1 := by simp [canonicalKripkeModel];

lemma def_rel₂ : x ≺ y ↔ y.1.2 ⊆ x.1.2 := by
  constructor;
  . intro h φ;
    contrapose!;
    simp only [iff_not_mem₂_mem₁]
    apply h;
  . intro h φ;
    contrapose!;
    simp only [iff_not_mem₁_mem₂]
    apply h;

lemma truthlemma : t ⊩ φ ↔ φ ∈ t.1.1 := by
  induction φ generalizing t with
  | hatom => tauto;
  | hfalsum => simp [not_mem₁_falsum];
  | hand φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_and, *];
  | hor φ ψ ihp ihq => simp [SaturatedConsistentTableau.iff_mem₁_or, *];
  | himp φ ψ ihp ihq =>
    constructor;
    . contrapose!;
      intro h;
      replace h := iff_not_mem₁_mem₂.mp h;
      obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := (insert φ t.1.1, {ψ})) $ by
        intro Γ Δ hΓ hΔ;
        by_contra hC;
        apply t.consistent (Γ := Γ.erase φ) (Δ := {φ 🡒 ψ}) ?_ ?_;
        . simp only [Finset.disj_singleton];
          apply FConj_DT.mpr;
          apply Context.deduct!
          replace hC := Context.weakening! (Δ := insert φ Γ) (by simp) $ FConj_DT.mp hC;
          rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ);
          . simp only [Finset.coe_eq_empty] at hΔ;
            subst hΔ;
            simp only [Finset.disj_empty, Finset.coe_erase, Set.insert_diff_singleton] at hC ⊢;
            exact of_O! hC;
          . simp only [Finset.coe_eq_singleton] at hΔ;
            subst hΔ;
            simpa using hC;
        . simpa using Set.iff_subset_insert_subset_diff.mp hΓ;
        . simpa;
      have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
      apply forces_imp.not.mpr;
      push_neg;
      use t';
      refine ⟨?_, ?_, ?_⟩;
      . assumption;
      . apply ihp.mpr;
        assumption;
      . apply ihq.not.mpr;
        apply iff_not_mem₁_mem₂.mpr;
        simp_all only [Set.singleton_subset_iff];
    . intro h t' htt' hp;
      replace hp := ihp.mp hp;
      have hpq := htt' h;
      apply ihq.mpr;
      apply iff_not_mem₂_mem₁.mp;
      apply not_mem₂ (Γ := {φ, φ 🡒 ψ});
      . simp only [Finset.coe_insert, Finset.coe_singleton];
        apply Set.doubleton_subset.mpr;
        tauto;
      . suffices 𝓢 ⊢ Finset.conj {φ, φ 🡒 ψ} 🡒 Finset.disj {ψ} by simpa;
        apply Entailment.CFConj_CDisj!_of_innerMDP (φ := φ) (ψ := ψ) <;> simp;

lemma iff_validates_provable : (canonicalKripkeModel 𝓢) ⊧ φ ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose!;
    intro h;
    obtain ⟨t', ht'⟩ := lindenbaum $ by
      show Tableau.Consistent 𝓢 (∅, {φ});
      simp only [Tableau.Consistent];
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      apply h;
      rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ);
      . simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ;
        subst hΓ hΔ;
        simp only [Finset.conj_empty, Finset.disj_empty] at hC;
        exact of_O! $ hC ⨀ verum!;
      . simp only [Set.subset_empty_iff, Finset.coe_eq_empty, Finset.coe_eq_singleton] at hΓ hΔ;
        subst hΓ hΔ;
        simp only [Finset.conj_empty, Finset.disj_singleton] at hC;
        exact hC ⨀ verum!;;
    apply KripkeModel.notValidates_of_exists_world_notForces
    use t';
    apply truthlemma.not.mpr;
    apply iff_not_mem₁_mem₂.mpr;
    simp_all;
  . intro h t;
    suffices φ ∈ t.1.1 by exact truthlemma.mpr this;
    exact mem₁_of_provable h;

end canonicalKripkeModel



namespace Int

variable [Consistent (Propositional.Int)]

theorem provable_of_forall_model_validates
  : (∀ {κ : Type 0}, [Nonempty κ] → ∀ M : KripkeModel κ ℕ, [M.Intuitionistic] → M ⊧ φ) → (Propositional.Int) ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_validates_provable.mp $ h _

lemma exists_model_of_unprovable (h : (Propositional.Int) ⊬ φ)
  : ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ M : KripkeModel κ ℕ, ∃ _ : M.Intuitionistic, ∃ w : M.world, w ⊮ φ := by
  contrapose! h;
  apply provable_of_forall_model_validates;
  apply h;

end Int


end LO.Propositional


end
