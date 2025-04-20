import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Classical.Basic
import Foundation.Propositional.ConsistentTableau

namespace LO.Propositional

open Semantics

namespace Hilbert.Cl.Classical

theorem soundness (h : Hilbert.Cl ⊢! φ) : Valid (Classical.Valuation ℕ) φ := by
  intro v;
  induction h using Hilbert.Deduction.rec! with
  | maxm h => rcases h with ⟨φ, (rfl | rfl), ⟨_, rfl⟩⟩ <;> { tauto; }
  | mdp ihφψ ihφ => exact ihφψ ihφ;
  | andElimL =>
    simp [Semantics.Realize, Formula.Classical.val]; tauto;
  | andElimR =>
    simp [Semantics.Realize, Formula.Classical.val];
  | orElim =>
    simp [Semantics.Realize, Formula.Classical.val]
    tauto;
  | _ => tauto;

lemma not_provable_of_exists_valuation : (∃ v : Classical.Valuation _, ¬(v ⊧ φ)) → ¬(Hilbert.Cl ⊢! φ) := by
  contrapose;
  push_neg;
  exact soundness;

section

open
  Entailment
  SaturatedConsistentTableau

def canonicalVal (T : SaturatedConsistentTableau Hilbert.Cl) : Classical.Valuation ℕ where
  val a := (.atom a) ∈ T.1.1

lemma truthlemma {T : SaturatedConsistentTableau Hilbert.Cl} : (canonicalVal T) ⊧ φ ↔ φ ∈ T.1.1 := by
  induction φ using Formula.rec' with
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

theorem completeness : (Valid (Classical.Valuation _) φ) → (Hilbert.Cl ⊢! φ) := by
  contrapose;
  intro h;
  obtain ⟨T, hT⟩ := lindenbaum (𝓢 := Hilbert.Cl) (t₀ := (∅, {φ})) $ by
    intro Γ Δ hΓ hΔ;
    by_contra hC;
    replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
    subst hΓ;
    exact h $ of_Disj₂!_of_mem_eq hΔ (hC ⨀ verum!);
  unfold Semantics.Valid;
  push_neg;
  use (canonicalVal T);
  apply truthlemma.not.mpr;
  apply iff_not_mem₁_mem₂.mpr;
  apply hT.2;
  tauto;

lemma exists_valuation_of_not_provable : ¬(Hilbert.Cl ⊢! φ) → ∃ v : Classical.Valuation _, ¬(v ⊧ φ) := by
  contrapose;
  push_neg;
  exact completeness;

end

end Hilbert.Cl.Classical

end LO.Propositional
