import Foundation.Modal.Formula
import Foundation.Modal.Entailment.Basic

namespace LO.Modal

open LO.Entailment
open Entailment

variable {α : Type*}

abbrev Logic (α) := Set (Modal.Formula α)

instance : Entailment (Formula α) (Logic α) := ⟨fun L φ ↦ PLift (φ ∈ L)⟩


namespace Logic

variable {L L₀ L₁ L₂ L₃ : Logic α}

section

protected class Substitution (L : Logic α) where
  subst {φ} (s) : L ⊢ φ → L ⊢ φ⟦s⟧

protected class IsQuasiNormal (L : Logic α) extends Entailment.Cl L, Entailment.HasAxiomK L, Entailment.HasDiaDuality L, L.Substitution where

protected class IsNormal (L : Logic α) extends L.IsQuasiNormal, Entailment.Necessitation L where
instance [L.IsNormal] : Entailment.K L where

end


section

variable {L : Logic α} {φ ψ : Formula α}

@[simp low]
lemma iff_provable : L ⊢! φ ↔ φ ∈ L := by
  constructor;
  . intro h;
    exact PLift.down h.some;
  . intro h;
    constructor;
    constructor;
    exact h;

@[simp low]
lemma iff_unprovable : L ⊬ φ ↔ φ ∉ L := by
  apply not_congr;
  simp [iff_provable];

lemma iff_equal_provable_equiv : L₁ = L₂ ↔ L₁ ≊ L₂ := by
  constructor;
  . tauto;
  . rintro h;
    ext φ;
    simpa using Equiv.iff.mp h φ;

lemma subst! [L.Substitution] (s : Substitution _) (hφ : L ⊢! φ) : L ⊢! φ⟦s⟧ := ⟨Substitution.subst s hφ.some⟩


section

variable [DecidableEq α] [L.IsQuasiNormal] [Consistent L]

@[simp]
lemma no_bot : L ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ := Consistent.exists_unprovable (𝓢 := L) inferInstance;
  by_contra! hC;
  apply hφ;
  apply of_O!;
  exact hC;

-- TODO: more general place
lemma not_neg_of! (hφ : L ⊢! φ) : L ⊬ ∼φ := by
  by_contra! hC;
  apply L.no_bot;
  exact hC ⨀ hφ;

end

end

end Logic


section

variable {L : Logic α}

instance : (∅ : Logic α) ⪯ L := ⟨by simp [Entailment.theory]⟩

instance [HasAxiomVerum L] : (∅ : Logic α) ⪱ L := by
  apply strictlyWeakerThan_iff.mpr;
  constructor;
  . simp;
  . use ⊤; constructor <;> simp;

instance : L ⪯ (Set.univ : Logic α) := ⟨by simp [Entailment.theory]⟩

instance [Consistent L] : L ⪱ (Set.univ : Logic α) := by
  apply strictlyWeakerThan_iff.mpr;
  constructor;
  . simp;
  . obtain ⟨φ, hφ⟩ := consistent_iff_exists_unprovable (𝓢 := L) |>.mp (by assumption);
    use φ;
    constructor;
    . assumption;
    . simp [Entailment.theory]

end

end LO.Modal
