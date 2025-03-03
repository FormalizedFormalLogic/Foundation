import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Classical.Basic
import Foundation.Propositional.ConsistentTableau

namespace LO.Propositional

namespace Hilbert.Cl.Classical

-- Semantics.Valid (Classical.Valuation ℕ) φ
lemma soundness (h : Hilbert.Cl ⊢! φ) : ∀ v, φ.val v := by
  induction h using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases h with ⟨φ, (rfl | rfl), ⟨_, rfl⟩⟩ <;> { intro v; tauto; }
  | mdp ihφψ ihφ => intro v; exact ihφψ v $ ihφ v;
  | orElim => simp [Formula.val]; tauto;
  | _ => simp_all [Formula.val];


section

open
  Entailment
  SaturatedConsistentTableau

def canonicalVal (T : SaturatedConsistentTableau Hilbert.Cl) : Classical.Valuation ℕ where
  val a := (.atom a) ∈ T.1.1

lemma truthlemma {T : SaturatedConsistentTableau Hilbert.Cl} : φ.val (canonicalVal T) ↔ φ ∈ T.1.1 := by
  induction φ using Formula.rec' with
  | hatom => simp [Formula.val, canonicalVal];
  | hfalsum => simp [Formula.val, canonicalVal];
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

lemma completeness : (∀ v, φ.val v) → (Hilbert.Cl ⊢! φ) := by
  contrapose;
  intro h;
  push_neg;
  obtain ⟨T, hT⟩ := lindenbaum (𝓢 := Hilbert.Cl) (t₀ := (∅, {φ})) $ by
    intro Γ Δ hΓ hΔ;
    by_contra hC;
    replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
    subst hΓ;
    exact h $ disj_allsame'! hΔ (hC ⨀ verum!);
  use (canonicalVal T);
  apply truthlemma.not.mpr;
  apply iff_not_mem₁_mem₂.mpr;
  apply hT.2;
  tauto;

end

end Hilbert.Cl.Classical

end LO.Propositional
