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
  (∀ C ∈ S.ant, x ⊩[M] C) → ∃ D ∈ S.suc, x ⊩[M] D

scoped[FFL.ProvabilityLogic.Kripke.Model.World]
  notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S

def Model.ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩[M] S

scoped[FFL.ProvabilityLogic.Kripke.Model]
  infix:45 " ⊧ " => Model.ValidateSequent

namespace Model

lemma validateSequent_singleton_iff :
    M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩[M] C) → x ⊩[M] A := by
  simp [ValidateSequent, ForcesSequent];

/-! ### Soundness of the propositional rules -/

@[grind .]
lemma validateSequent_axm : M ⊧ ({A} ⟹ {A}) := fun _ hx ↦ ⟨A, by simp, hx A (by simp)⟩

@[grind .]
lemma validateSequent_botL : M ⊧ ({⊥} ⟹ ∅) := fun _ hx ↦ absurd (hx ⊥ (by simp)) not_forces_bot

@[grind →]
lemma validateSequent_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') : M ⊧ (Γ' ⟹ Δ) :=
  fun x hx ↦ h x (fun C hC ↦ hx C (hΓ hC))

@[grind →]
lemma validateSequent_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ') : M ⊧ (Γ ⟹ Δ') := by
  intro x hx;
  obtain ⟨D, hD, hxD⟩ := h x hx;
  exact ⟨D, hΔ hD, hxD⟩;

variable [DecidableEq α]

@[grind →]
lemma validateSequent_impL (h₁ : M ⊧ (Γ ⟹ insert A Δ)) (h₂ : M ⊧ (insert B Γ ⟹ Δ)) :
    M ⊧ (insert (A 🡒 B) Γ ⟹ Δ) := by
  intro x hx;
  have hΓ : ∀ C ∈ Γ, x ⊩[M] C := fun C hC ↦ hx C (by simp [hC]);
  by_cases hA : x ⊩[M] A;
  . exact h₂ x (by simpa [hx _ (Finset.mem_insert_self _ _) hA] using hΓ);
  . obtain ⟨D, hD, hxD⟩ := h₁ x hΓ;
    grind;

@[grind →]
lemma validateSequent_impR (h : M ⊧ (insert A Γ ⟹ insert B Δ)) : M ⊧ (Γ ⟹ insert (A 🡒 B) Δ) := by
  intro x hx;
  by_cases hA : x ⊩[M] A;
  . obtain ⟨D, hD, hxD⟩ := h x (by simpa [hA] using hx);
    rcases Finset.mem_insert.mp hD with rfl | hD;
    . exact ⟨A 🡒 D, by simp, fun _ ↦ hxD⟩;
    . grind;
  . exact ⟨A 🡒 B, by simp, fun h ↦ absurd h hA⟩;

end Model

end FFL.ProvabilityLogic.Kripke

end
