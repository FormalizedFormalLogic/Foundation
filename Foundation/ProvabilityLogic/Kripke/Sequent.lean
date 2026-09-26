module

public import Foundation.ProvabilityLogic.Kripke.Basic
public import Foundation.ProvabilityLogic.Sequent

/-!
# Kripke semantics of sequents
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

def Model.World.ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ C ∈ S.ant, x ⊩[_] C) → ∃ D ∈ S.suc, x ⊩[_] D

scoped[FFL.ProvabilityLogic.Kripke.Model.World]
  notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S

def Model.ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩[_] S

scoped[FFL.ProvabilityLogic.Kripke.Model]
  infix:45 " ⊧ " => Model.ValidateSequent

namespace Model.World

variable {x : M.World}

@[grind .] lemma forcesSequent_axm : x ⊩[_] ({A} ⟹ {A}) := fun hx ↦ ⟨A, by simp, hx A (by simp)⟩

@[grind .] lemma forcesSequent_botL : x ⊩[_] ({⊥} ⟹ ∅) := fun hx ↦ absurd (hx ⊥ (by simp)) id

@[grind →]
lemma forcesSequent_wkL (h : x ⊩[_] (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') : x ⊩[_] (Γ' ⟹ Δ) :=
  fun hx ↦ h fun C hC ↦ hx C (hΓ hC)

@[grind →]
lemma forcesSequent_wkR (h : x ⊩[_] (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ') : x ⊩[_] (Γ ⟹ Δ') :=
  fun hx ↦ (h hx).imp fun _ hD ↦ ⟨hΔ hD.1, hD.2⟩

end Model.World

section

variable [DecidableEq α]

namespace Model.World

variable {x : M.World}

@[grind →]
lemma forcesSequent_impL (h₁ : x ⊩[_] (Γ ⟹ insert A Δ)) (h₂ : x ⊩[_] (insert B Γ ⟹ Δ)) :
    x ⊩[_] (insert (A 🡒 B) Γ ⟹ Δ) := by
  intro hx;
  have hΓ : ∀ C ∈ Γ, x ⊩[_] C := fun C hC ↦ hx C (by simp [hC]);
  by_cases hA : x ⊩[_] A;
  · exact h₂ (by simpa [hx _ (Finset.mem_insert_self _ _) hA] using hΓ);
  · obtain ⟨D, hD, hxD⟩ := h₁ hΓ;
    grind;

@[grind →]
lemma forcesSequent_impR (h : x ⊩[_] (insert A Γ ⟹ insert B Δ)) :
    x ⊩[_] (Γ ⟹ insert (A 🡒 B) Δ) := by
  intro hx;
  by_cases hA : x ⊩[_] A;
  · obtain ⟨D, hD, hxD⟩ := h (by simpa [hA] using hx);
    rcases Finset.mem_insert.mp hD with rfl | hD;
    · exact ⟨A 🡒 D, by simp, fun _ ↦ hxD⟩;
    · grind;
  · exact ⟨A 🡒 B, by simp, fun h ↦ absurd h hA⟩;

@[grind →]
lemma forcesSequent_cut {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α}
    (h₁ : x ⊩[_] (Γ₁ ⟹ insert A Δ₁)) (h₂ : x ⊩[_] (insert A Γ₂ ⟹ Δ₂)) :
    x ⊩[_] (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := by
  intro hx;
  obtain ⟨D, hD, hxD⟩ := h₁ fun C hC ↦ hx C (by simp [hC]);
  rcases Finset.mem_insert.mp hD with rfl | hD;
  · obtain ⟨E, hE, hxE⟩ := h₂ (by
      intro C hC;
      rcases Finset.mem_insert.mp hC with rfl | hC;
      · exact hxD;
      · exact hx C (by simp [hC]));
    exact ⟨E, by simp [hE], hxE⟩;
  · exact ⟨D, by simp [hD], hxD⟩;

end Model.World

end

namespace Model

lemma validateSequent_singleton_iff :
    M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩[_] C) → x ⊩[_] A := by
  simp [ValidateSequent, ForcesSequent];

/-! ### Soundness of the propositional rules -/

@[grind .]
lemma validateSequent_axm : M ⊧ ({A} ⟹ {A}) := fun _ ↦ forcesSequent_axm

@[grind .]
lemma validateSequent_botL : M ⊧ ({⊥} ⟹ ∅) := fun _ ↦ forcesSequent_botL

@[grind →]
lemma validateSequent_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') : M ⊧ (Γ' ⟹ Δ) :=
  fun x ↦ forcesSequent_wkL (h x) hΓ

@[grind →]
lemma validateSequent_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ') : M ⊧ (Γ ⟹ Δ') :=
  fun x ↦ forcesSequent_wkR (h x) hΔ

variable [DecidableEq α]

@[grind →]
lemma validateSequent_impL (h₁ : M ⊧ (Γ ⟹ insert A Δ)) (h₂ : M ⊧ (insert B Γ ⟹ Δ)) :
    M ⊧ (insert (A 🡒 B) Γ ⟹ Δ) := fun x ↦ forcesSequent_impL (h₁ x) (h₂ x)

@[grind →]
lemma validateSequent_impR (h : M ⊧ (insert A Γ ⟹ insert B Δ)) : M ⊧ (Γ ⟹ insert (A 🡒 B) Δ) :=
  fun x ↦ forcesSequent_impR (h x)

end Model

end FFL.ProvabilityLogic.Kripke

end
