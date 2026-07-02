module

public import Foundation.Modal.MaximalConsistentSet
public import Foundation.Modal.PLoN.Basic

@[expose] public section

namespace LO.Modal

variable {S} [Entailment S (Formula ℕ)]
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

variable {φ : Formula ℕ}

lemma truthlemma : ∀ {X : (canonicalModel 𝓢).World}, X ⊩ φ ↔ (φ ∈ X) := by
  induction φ with
  | hfalsum => simp [PLoN.Forces];
  | hatom => simp [PLoN.Forces];
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
      contrapose! h;
      obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (T := {∼φ}) (not_singleton_consistent X.consistent (iff_mem_neg.mpr h));
      apply PLoN.Forces.not_box_def.mpr;
      use Y;
      constructor;
      . constructor;
        . exact iff_mem_neg.mpr h;
        . tauto_set;
      . apply (@ih Y).not.mpr;
        apply iff_mem_neg.mp;
        tauto_set;
    . intro h Y RXY;
      have : □φ ∉ X := iff_mem_neg.mp RXY.1;
      contradiction;

def instComplete_of_mem_canonicalFrame {C : PLoN.FrameClass} (h : (canonicalFrame 𝓢) ∈ C) : Complete 𝓢 C := by
  constructor;
  intro φ;
  contrapose!;
  intro h;
  obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (T := {∼φ}) $ unprovable_iff_singleton_neg_consistent.mpr h;
  apply PLoN.not_validOnFrameClass_of_exists_model_world;
  use (canonicalModel 𝓢), Y;
  constructor;
  . assumption;
  . apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    tauto_set;

end PLoN

end LO.Modal
end
