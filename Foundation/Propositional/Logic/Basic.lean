import Foundation.Propositional.Formula
import Foundation.Modal.Entailment.Basic

namespace LO.Propositional

open LO.Entailment
open Entailment

abbrev Logic (α) := Set (Propositional.Formula α)

instance : Entailment (Logic α) (Formula α) := ⟨fun L φ ↦ PLift (φ ∈ L)⟩

namespace Logic

variable {L L₀ L₁ L₂ L₃ : Logic α} {φ ψ : Formula α}

protected class Substitution (L : Logic α) where
  subst {φ : Formula _} (s) : L ⊢ φ → L ⊢ φ⟦s⟧

protected class Superintuitionistic (L : Logic α) extends Entailment.Int L, L.Substitution where

section

export Substitution (subst)

 @[grind =]
lemma iff_provable : L ⊢ φ ↔ φ ∈ L := by
  constructor;
  . intro h;
    exact PLift.down h.some;
  . intro h;
    constructor;
    constructor;
    exact h;

 @[grind =]
 lemma iff_unprovable : L ⊬ φ ↔ φ ∉ L := by grind

lemma iff_equal_provable_equiv : L₁ = L₂ ↔ L₁ ≊ L₂ := by
  constructor;
  . tauto;
  . rintro h;
    ext φ;
    have := Equiv.iff.mp h φ;
    grind;

lemma weakerThan_of_provable (h : ∀ φ, L₁ ⊢ φ → L₂ ⊢ φ) : L₁ ⪯ L₂ := by
  constructor;
  simpa [Entailment.theory, forall_exists_index];

lemma weakerThan_of_subset (h : L₁ ⊆ L₂) : L₁ ⪯ L₂ := by
  apply weakerThan_of_provable;
  grind;

section

variable [L.Superintuitionistic] [Consistent L]

@[simp, grind .]
lemma no_bot : L ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ := Consistent.exists_unprovable (𝓢 := L) inferInstance;
  by_contra! hC;
  apply hφ;
  apply of_O!;
  exact hC;

-- TODO: more general place
@[grind →]
lemma not_neg_of! (hφ : L ⊢ φ) : L ⊬ ∼φ := by
  by_contra! hC;
  apply L.no_bot;
  exact hC ⨀ hφ;

end

end
end Logic


section

variable {L : Logic α}

instance : (∅ : Logic α) ⪯ L := ⟨by simp [Entailment.theory, Logic.iff_provable]⟩

instance [HasAxiomVerum L] : (∅ : Logic α) ⪱ L := by
  apply strictlyWeakerThan_iff.mpr;
  constructor;
  . simp [Logic.iff_provable];
  . use ⊤;
    constructor;
    . simp [Logic.iff_unprovable];
    . exact Entailment.verum!;

instance : L ⪯ (Set.univ : Logic α) := ⟨by simp [Entailment.theory, Logic.iff_provable]⟩

instance [Consistent L] : L ⪱ (Set.univ : Logic α) := by
  apply strictlyWeakerThan_iff.mpr;
  constructor;
  . simp [Logic.iff_provable];
  . obtain ⟨φ, hφ⟩ := consistent_iff_exists_unprovable (𝓢 := L) |>.mp (by assumption);
    use φ;
    constructor;
    . assumption;
    . simp [Logic.iff_provable]

end

end LO.Propositional
