import Foundation.Modal.Formula

namespace LO.Modal

abbrev Logic (α) := Set (Modal.Formula α)


instance : Entailment (Formula α) (Logic α) := ⟨fun L φ ↦ PLift (φ ∈ L)⟩


namespace Logic

section

/-
protected class ModusPonens (L : Logic) where
  mdp_closed {φ ψ} : L ⊢! φ ➝ ψ → L ⊢! φ → L ⊢! ψ
-/

protected class Substitution (L : Logic α) where
  subst {φ} : L ⊢ φ → ∀ s, L ⊢ φ⟦s⟧


/-
protected class Necessitation (L : Logic) where
  nec_closed {φ} : φ ∈ L → □φ ∈ L

protected class Unnecessitation (L : Logic) where
  unnec_closed {φ} : □φ ∈ L → φ ∈ L

protected class ModalDisjunctive (L : Logic) where
  modal_disjunctive_closed {φ ψ} : □φ ⋎ □ψ ∈ L → φ ∈ L ∨ ψ ∈ L
-/

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

lemma subst! [L.Substitution] (hφ : L ⊢! φ) (s : Substitution _) : L ⊢! φ⟦s⟧ := ⟨Substitution.subst hφ.some s⟩

end

end Logic


section

variable {α} {L : Logic α}

open Entailment

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
