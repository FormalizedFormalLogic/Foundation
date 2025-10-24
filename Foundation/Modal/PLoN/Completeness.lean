import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.PLoN.Basic

namespace LO.Modal

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢] [Entailment.Necessitation 𝓢]

namespace PLoN

open Formula
open FormulaSet
open MaximalConsistentSet

abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢] : PLoN.Frame where
  World := MaximalConsistentSet 𝓢
  Rel := λ φ Ω₁ Ω₂ => ∼(□φ) ∈ Ω₁ ∧ ∼φ ∈ Ω₂

abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢] : PLoN.Model where
  toFrame := canonicalFrame 𝓢
  Valuation Ω a := (atom a) ∈ Ω

@[reducible] instance : Semantics (Formula ℕ) (canonicalModel 𝓢).World := Formula.PLoN.Satisfies.semantics (M := canonicalModel 𝓢)

variable {φ : Formula ℕ}

lemma truthlemma : ∀ {X : (canonicalModel 𝓢).World}, X ⊧ φ ↔ (φ ∈ X) := by
  induction φ with
  | hfalsum =>
    simp only [Semantics.Models, PLoN.Satisfies, false_iff];
    exact not_mem_falsum;
  | hatom =>
    simp_all [Semantics.Models, PLoN.Satisfies];
  | himp φ ψ ihp ihq =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_imp.mpr;
      intro hp; replace hp := ihp.mpr hp;
      exact ihq.mp $ h hp;
    . intro h;
      have := iff_mem_imp.mp h;
      intro hp; replace hp := ihp.mp hp;
      exact ihq.mpr $ this hp
  | hbox φ ih =>
    intro X;
    constructor;
    . intro h;
      by_contra hC;
      obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (T := {∼φ}) (not_singleton_consistent X.consistent (iff_mem_neg.mpr hC));
      suffices ¬X ⊧ □φ by contradiction;
      suffices ∃ Y, (X ≺[φ] Y) ∧ (¬Y ⊧ φ) by
        apply PLoN.Satisfies.box_def.not.mpr;
        push_neg;
        exact this;
      use Y;
      constructor;
      . constructor;
        . exact iff_mem_neg.mpr hC;
        . tauto_set;
      . apply (@ih Y).not.mpr;
        apply iff_mem_neg.mp;
        tauto_set;
    . intro h Y RXY;
      have : □φ ∉ X := iff_mem_neg.mp RXY.1;
      contradiction;

class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢] (C : FrameClass) : Prop where
  canonical : (canonicalFrame 𝓢) ∈ C

instance [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply PLoN.ValidOnFrameClass.not_of_exists_model;
  use (canonicalModel 𝓢);
  constructor;
  . exact Canonical.canonical;
  . suffices ∃ X, ¬(PLoN.Satisfies (canonicalModel 𝓢) X φ) by
      simpa only [Semantics.Models, PLoN.ValidOnModel, not_forall];
    obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (T := {∼φ}) $ by
      apply unprovable_iff_singleton_neg_consistent.mpr;
      exact h;
    use Y;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    tauto_set;
⟩

end PLoN

end LO.Modal
