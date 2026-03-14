module

public import Foundation.Modal.Formula.Basic
public import Foundation.Modal.Entailment.Basic
public import Foundation.Meta.ClProver

@[expose] public section

namespace LO.Modal

open LO.Entailment
open Entailment

variable {α : Type*}

abbrev Logic (α) := Set (Modal.Formula α)

instance : Entailment (Logic α) (Formula α) := ⟨fun L φ ↦ PLift (φ ∈ L)⟩


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

export Substitution (subst)
attribute [grind <=] subst

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

@[simp, grind .]
lemma mem_verum [HasAxiomVerum L] : ⊤ ∈ L := by
  apply iff_provable.mp;
  exact verum!;

section

variable [Consistent L]

lemma exists_unprovable : ∃ φ, L ⊬ φ := Consistent.exists_unprovable (𝓢 := L) inferInstance

variable [DecidableEq α] [L.IsQuasiNormal]

@[simp, grind .]
lemma no_bot : L ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ := exists_unprovable (L := L);
  contrapose! hφ;
  apply of_O!;
  assumption;

@[simp, grind .]
lemma not_mem_bot : ⊥ ∉ L := by
  apply iff_unprovable.mp;
  exact no_bot;

-- TODO: more general place
@[grind →]
lemma not_neg_of! (hφ : L ⊢ φ) : L ⊬ ∼φ := by
  by_contra! hC;
  apply L.no_bot;
  exact hC ⨀ hφ;

end


lemma weakerThan_of_provable (h : ∀ φ, L₁ ⊢ φ → L₂ ⊢ φ) : L₁ ⪯ L₂ := by
  constructor;
  simpa [Entailment.theory, forall_exists_index];

lemma weakerThan_of_subset (h : L₁ ⊆ L₂) : L₁ ⪯ L₂ := by
  apply weakerThan_of_provable;
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

@[simp, grind .]
lemma subset_of_weakerThan [L₁ ⪯ L₂] : L₁ ⊆ L₂ := by
  intro φ;
  suffices L₁ ⊢ φ → L₂ ⊢ φ by grind;
  exact Entailment.WeakerThan.pbl;

instance [L₁ ≊ L₂] : L₁ ⪯ L₂ := Equiv.le inferInstance
instance [L₁ ≊ L₂] : L₂ ⪯ L₁ := Equiv.le $ .symm inferInstance

@[simp, grind .] lemma eq_of_equiv [L₁ ≊ L₂] : L₁ = L₂ := Set.Subset.antisymm subset_of_weakerThan subset_of_weakerThan

end

section

variable [DecidableEq α] [Entailment.Cl L]

lemma lconj_subst {X : List (Formula α)} {s : Substitution α} : L ⊢ (X.map (·⟦s⟧)).conj₂ 🡒 X.conj₂⟦s⟧ := by
  induction X using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ X hφ ih =>
    suffices L ⊢ φ⟦s⟧ ⋏ ⋀(X.map (·⟦s⟧)) 🡒 φ⟦s⟧ ⋏ (⋀X)⟦s⟧ by
      simpa [List.conj₂_cons_nonempty hφ, List.conj₂_cons_nonempty (show X.map (·⟦s⟧) ≠ [] by simpa)];
    cl_prover [ih];

lemma fconj_subst {X : Finset (Formula α)} {s : Substitution α} : L ⊢ (X.image (·⟦s⟧)).conj 🡒 X.conj⟦s⟧ := by
  apply C!_trans ?_ $ lconj_subst (L := L) (X := X.toList) (s := s);
  apply right_Conj₂!_intro;
  intro φ hφ;
  apply left_Fconj!_intro;
  simp_all;

end

end Logic


section

variable {L : Logic α}

instance : (∅ : Logic α) ⪯ L := Logic.weakerThan_of_subset (by tauto_set)

instance [HasAxiomVerum L] : (∅ : Logic α) ⪱ L := by
  apply Logic.strictWeakerThan_of_ssubset;
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . grind;
  . use ⊤;
    grind;

instance : L ⪯ (Set.univ : Logic α) := Logic.weakerThan_of_subset (by tauto_set)

instance [Consistent L] : L ⪱ (Set.univ : Logic α) := by
  apply Logic.strictWeakerThan_of_ssubset;
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . simp;
  . obtain ⟨φ, hφ⟩ := L.exists_unprovable;
    use φ;
    grind;

end



end LO.Modal
end
