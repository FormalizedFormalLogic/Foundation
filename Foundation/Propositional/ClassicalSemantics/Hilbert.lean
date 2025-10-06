import Foundation.Propositional.Hilbert.Basic
import Foundation.Propositional.ClassicalSemantics.Basic
import Foundation.Propositional.ConsistentTableau

namespace LO.Propositional

open Semantics
open ClassicalSemantics
open Formula.ClassicalSemantics

namespace Cl

theorem soundness (h : Propositional.Cl ⊢ φ) : φ.isTautology := by
  intro v;
  induction h with
  | axm _ h => rcases h with (rfl | rfl) <;> tauto;
  | mdp ihφψ ihφ => exact ihφψ ihφ;
  | andElimL => simp [Semantics.Realize, val]; tauto;
  | andElimR => simp [Semantics.Realize, val];
  | orElim => simp [Semantics.Realize, val]; tauto;
  | _ => tauto;

lemma not_provable_of_exists_valuation : (∃ v : Valuation _, ¬(v ⊧ φ)) → Propositional.Cl ⊬ φ := by
  contrapose!;
  simpa using soundness;

section Completeness

open
  Entailment
  SaturatedConsistentTableau

def canonicalVal (T : SaturatedConsistentTableau Propositional.Cl) : Valuation ℕ := λ a => (.atom a) ∈ T.1.1

lemma truthlemma {T : SaturatedConsistentTableau Propositional.Cl} : (canonicalVal T) ⊧ φ ↔ φ ∈ T.1.1 := by
  induction φ with
  | hatom => simp [canonicalVal];
  | hfalsum => simp [canonicalVal];
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

theorem completeness : (φ.isTautology) → (Propositional.Cl ⊢ φ) := by
  contrapose;
  intro h;
  obtain ⟨T, hT⟩ := lindenbaum (𝓢 := Propositional.Cl) (t₀ := (∅, {φ})) $ by
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
  unfold Formula.isTautology Semantics.Valid;
  push_neg;
  use (canonicalVal T);
  apply truthlemma.not.mpr;
  apply iff_not_mem₁_mem₂.mpr;
  apply hT.2;
  tauto;

@[grind]
theorem iff_isTautology_provable : φ.isTautology ↔ Propositional.Cl ⊢ φ := ⟨
  completeness,
  soundness,
⟩

lemma exists_valuation_of_not_provable : ¬(Propositional.Cl ⊢ φ) → ∃ v : Valuation _, ¬(v ⊧ φ) := by
  contrapose!;
  simpa using completeness;

end Completeness

theorem tautologies : Propositional.Cl = { φ | φ.isTautology } := by
  ext φ;
  simp [Cl.iff_isTautology_provable, Logic.iff_provable];

end Cl


end LO.Propositional
