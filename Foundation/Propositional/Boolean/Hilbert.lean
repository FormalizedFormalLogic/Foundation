module

public import Foundation.Propositional.Boolean.Basic
public import Foundation.Propositional.ConsistentTableau
public import Foundation.Propositional.Hilbert.Minimal.Basic

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open Semantics
open Boolean
open Formula.Boolean

variable {α} {φ : Formula α}

namespace Hilbert.Cl

theorem tautology_of_provable : Hilbert.Cl ⊢ φ → φ.IsTautology := by
  rintro ⟨h⟩ v;
  induction h with
  | axm h => rcases h with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> tauto;
  | mdp _ _ ihφψ ihφ => exact ihφψ ihφ;
  | andElimL => simp [Semantics.Models, val]; tauto;
  | andElimR => simp [Semantics.Models, val];
  | orElim => simp [Semantics.Models, val]; tauto;
  | _ => tauto;
alias soundness := tautology_of_provable

lemma not_provable_of_exists_valuation : (∃ v : Valuation _, ¬(v ⊧ φ)) → Hilbert.Cl ⊬ φ := by
  contrapose!;
  apply tautology_of_provable;


section completeness

open
  Entailment
  SaturatedConsistentTableau

variable [DecidableEq α] [Encodable α] {φ : Formula α}

def canonicalVal (T : SaturatedConsistentTableau (Hilbert.Cl : Hilbert α)) : Valuation α := λ a => (.atom a) ∈ T.1.1

lemma truthlemma {T : SaturatedConsistentTableau (Hilbert.Cl : Hilbert α)} : (canonicalVal T) ⊧ φ ↔ φ ∈ T.1.1 := by
  induction φ with
  | hatom => simp [canonicalVal];
  | hfalsum => simp
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ;
      rcases imp_iff_not_or.mp hφψ with hφ | hψ;
      . apply iff_mem₁_imp.mpr;
        left;
        exact iff_not_mem₁_mem₂.mp $ ihφ.not.mp $ hφ;
      . apply iff_mem₁_imp.mpr;
        right;
        exact ihψ.mp hψ;
    . rintro hφψ hφ;
      apply ihψ.mpr;
      rcases iff_mem₁_imp.mp hφψ with hφ | hψ;
      . have := ihφ.not.mpr $ iff_not_mem₁_mem₂.mpr hφ; contradiction;
      . exact hψ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply iff_mem₁_and.mpr;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . rintro hφψ;
      rcases iff_mem₁_and.mp hφψ with ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . apply iff_mem₁_or.mpr;
        left;
        apply ihφ.mp hφ;
      . apply iff_mem₁_or.mpr;
        right;
        apply ihψ.mp hψ;
    . rintro hφψ;
      rcases iff_mem₁_or.mp hφψ with hφ | hψ;
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;

theorem provable_of_tautology : (φ.IsTautology) → (Hilbert.Cl ⊢ φ) := by
  contrapose;
  intro h;
  obtain ⟨T, hT⟩ := lindenbaum (𝓢 := Hilbert.Cl) (t₀ := (∅, {φ})) $ by
    intro Γ Δ hΓ hΔ;
    by_contra hC;
    apply h;
    replace hΓ : Γ = ∅ := by simpa using hΓ;
    subst hΓ;
    rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ);
    . simp only [Finset.coe_eq_empty] at hΔ;
      subst hΔ;
      exact of_O! $ (by simpa using hC) ⨀ verum!;
    . simp only [Finset.coe_eq_singleton] at hΔ;
      subst hΔ;
      exact (by simpa using hC) ⨀ verum!;
  dsimp [Formula.IsTautology, Valid];
  push_neg;
  use (canonicalVal T);
  apply truthlemma.not.mpr;
  apply iff_not_mem₁_mem₂.mpr;
  apply hT.2;
  tauto;
alias completeness := provable_of_tautology

@[grind =]
theorem iff_provable_tautology : Hilbert.Cl ⊢ φ ↔ φ.IsTautology := ⟨soundness, completeness⟩

lemma exists_valuation_of_not_provable : Hilbert.Cl ⊬ φ → ∃ v : Valuation _, ¬(v ⊧ φ) := by
  contrapose!;
  apply completeness;

end completeness

end Hilbert.Cl

@[grind =]
lemma Cl.iff_mem_tautology [DecidableEq α] [Encodable α] : φ ∈ Propositional.Cl ↔ φ.IsTautology :=
  Iff.trans Hilbert.iff_mem_logic_provable $ Hilbert.Cl.iff_provable_tautology

end LO.Propositional

end
