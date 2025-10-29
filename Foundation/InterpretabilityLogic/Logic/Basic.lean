import Foundation.Modal.Logic.Basic
import Foundation.InterpretabilityLogic.Formula.Substitution

namespace LO.InterpretabilityLogic

open LO.Entailment
open Entailment

variable {α : Type*}

abbrev Logic (α) := Set (InterpretabilityLogic.Formula α)

instance : Entailment (Logic α) (Formula α) := ⟨fun L φ ↦ PLift (φ ∈ L)⟩


namespace Logic

variable {L L₀ L₁ L₂ L₃ : Logic α}



section

protected class Substitution (L : Logic α) where
  subst {φ} (s) : L ⊢ φ → L ⊢ φ⟦s⟧

export Substitution (subst)

end


section

variable {L : Logic α} {φ ψ : Formula α}


@[grind]
lemma iff_provable : L ⊢ φ ↔ φ ∈ L := by
  constructor;
  . intro h;
    exact PLift.down h.some;
  . intro h;
    constructor;
    constructor;
    exact h;

@[grind]
lemma iff_unprovable : L ⊬ φ ↔ φ ∉ L := by
  apply not_congr;
  simp [iff_provable];

lemma iff_equal_provable_equiv : L₁ = L₂ ↔ L₁ ≊ L₂ := by
  constructor;
  . tauto;
  . rintro h;
    ext φ;
    have := Equiv.iff.mp h φ;
    grind;

@[simp]
lemma mem_verum [HasAxiomVerum L] : ⊤ ∈ L := by
  apply iff_provable.mp;
  simp;


section

variable [Consistent L]

lemma exists_unprovable : ∃ φ, L ⊬ φ := Consistent.exists_unprovable (𝓢 := L) inferInstance

variable [DecidableEq α] [Entailment.Cl L]

@[simp, grind]
lemma no_bot : L ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ := exists_unprovable (L := L);
  contrapose! hφ;
  apply of_O! hφ;

@[simp, grind]
lemma not_mem_bot : ⊥ ∉ L := by
  apply iff_unprovable.mp;
  exact no_bot;

-- TODO: more general place
@[grind]
lemma not_neg_of! (hφ : L ⊢ φ) : L ⊬ ∼φ := by
  by_contra! hC;
  apply L.no_bot;
  exact hC ⨀ hφ;

end


lemma weakerThan_of_provable (h : ∀ φ, L₁ ⊢ φ → L₂ ⊢ φ) : L₁ ⪯ L₂ := by
  constructor;
  simpa [Entailment.theory, forall_exists_index];

lemma weakerThan_of_subset (h : L₁ ⊆ L₂) : L₁ ⪯ L₂ := by
  suffices ∀ (φ : Formula α), L₁ ⊢ φ → L₂ ⊢ φ by apply weakerThan_of_provable this;
  intro φ;
  grind;

lemma equiv_of_provable (h : ∀ φ, L₁ ⊢ φ ↔ L₂ ⊢ φ) : L₁ ≊ L₂ := by
  apply Entailment.Equiv.antisymm;
  constructor <;>
  . apply weakerThan_of_provable;
    grind;

lemma strictWeakerThan_of_ssubset (h : L₁ ⊂ L₂) : L₁ ⪱ L₂ := by
  apply Entailment.strictlyWeakerThan_iff.mpr;
  obtain ⟨h₁, ⟨ψ, hψ⟩⟩ := Set.ssubset_iff_exists.mp h;
  constructor;
  . intro φ hφ; exact weakerThan_of_subset h.1 |>.pbl hφ;
  . use ψ;
    grind;

@[simp, grind]
lemma subset_of_weakerThan [L₁ ⪯ L₂] : L₁ ⊆ L₂ := by
  intro φ;
  suffices L₁ ⊢ φ → L₂ ⊢ φ by grind;
  exact Entailment.WeakerThan.pbl;

instance [L₁ ≊ L₂] : L₁ ⪯ L₂ := Equiv.le inferInstance
instance [L₁ ≊ L₂] : L₂ ⪯ L₁ := Equiv.le $ .symm inferInstance

@[simp, grind]
lemma eq_of_equiv [L₁ ≊ L₂] : L₁ = L₂ := Set.Subset.antisymm subset_of_weakerThan subset_of_weakerThan

end

end Logic

end LO.InterpretabilityLogic
