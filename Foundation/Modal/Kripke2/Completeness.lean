module

public import Foundation.Modal.Tableau
public import Foundation.Modal.Kripke2.Basic

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open MaximalConsistentTableau
open KripkeModel

variable [DecidableEq α] [Encodable α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]
variable {φ ψ : Formula α}

@[grind]
def canonicalKripkeModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : KripkeModel (MaximalConsistentTableau 𝓢) α where
  rel t₁ t₂ := □⁻¹'t₁.1.1 ⊆ t₂.1.1
  val a t := (atom a) ∈ t.1.1

attribute [grind .]
  MaximalConsistentTableau.not_mem₁_falsum
  MaximalConsistentTableau.mem₂_falsum
attribute [grind =] MaximalConsistentTableau.iff_mem₁_imp
attribute [grind =] MaximalConsistentTableau.iff_not_mem₁_mem₂
attribute [grind =]
  MaximalConsistentTableau.iff_mem₁_box
  MaximalConsistentTableau.iff_mem₂_box

namespace canonicalKripkeModel

variable {t : (canonicalKripkeModel 𝓢).world}

lemma truthlemma : (φ ∈ t.1.1 ↔ t ⊩ φ) ∧ (φ ∈ t.1.2 ↔ t ⊮ φ) := by
  induction φ generalizing t with
  | hatom | hfalsum | himp => grind;
  | hbox φ ihφ =>
    constructor;
    . constructor;
      . intro h t' Rtt';
        apply ihφ.1.1;
        grind;
      . intro h;
        apply iff_mem₁_box.mpr;
        intro t' Rtt';
        apply ihφ.1.2;
        exact h t' Rtt';
    . constructor;
      . intro h;
        apply forces_box.not.mpr;
        push_neg;
        obtain ⟨t', Rtt', ht'⟩ := iff_mem₂_box.mp h;
        use t';
        grind;
      . intro h;
        apply iff_mem₂_box.mpr;
        replace h := forces_box.not.mp h;
        grind;

@[grind =] lemma truthlemma₁ : φ ∈ t.1.1 ↔ t ⊩ φ := truthlemma.1
@[grind =] lemma truthlemma₂ : φ ∈ t.1.2 ↔ t ⊮ φ := truthlemma.2

@[grind =]
lemma iff_valid_provable : (canonicalKripkeModel 𝓢) ⊧ φ ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose!;
    intro h;
    have : Tableau.Consistent 𝓢 (∅, {φ}) := by
      apply Tableau.iff_consistent_empty_singleton₂.mpr;
      exact h;
    obtain ⟨t, ht⟩ := lindenbaum this;
    apply notModels_of_exists_world_notForces;
    use t;
    apply truthlemma₂.mp;
    apply ht.2;
    tauto_set;
  . intro h t;
    exact truthlemma₁.mp $ MaximalConsistentTableau.iff_provable_mem₁.mp h t;

end canonicalKripkeModel

end LO.Modal

end
