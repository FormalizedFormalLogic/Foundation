module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.GL.Hilbert.Basic

/-!
# The logic `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

abbrev Logic.GL {α : Type*} : Logic α := { A | ⊢ᴴ[GL] A }

notation "𝐆𝐋" => Logic.GL

namespace Logic.GL

open Entailment in
/-- A quasi-normal extension of `GL` contains `A` if it contains `Γ` and `Γ.conj 🡒 A ∈ 𝐆𝐋`. -/
lemma mem_sumQuasiNormal_of_conj {α : Type*} [DecidableEq α] {L : Logic α} {Γ : FormulaFinset α}
    (hΓ : ∀ B ∈ Γ, B ∈ 𝐆𝐋 +ᴸ L) : ∀ {A}, Γ.conj 🡒 A ∈ 𝐆𝐋 → A ∈ 𝐆𝐋 +ᴸ L := by
  induction Γ using Finset.induction_on with
  | empty =>
    intro A h;
    have h₁ : ⊢ᴴ[GL] (∅ : FormulaFinset α).conj 🡒 A := h;
    have h₂ : ⊢ᴴ[GL] (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact .mem₁ (h₁ ⨀ h₂);
  | insert B Γ _ ih =>
    intro A h;
    have h₁ : ⊢ᴴ[GL] (insert B Γ).conj 🡒 A := h;
    have h₂ : ⊢ᴴ[GL] B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    have h₃ : ⊢ᴴ[GL] Γ.conj 🡒 B 🡒 A := by cl_prover [h₁, h₂];
    exact .mdp (ih (fun C hC ↦ hΓ C (by simp [hC])) h₃) (hΓ B (by simp));

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem provability_TFAE : [
    A ∈ 𝐆𝐋,
    ⊢ᴴ[GL] A,
    ⊢ᴳ[GL] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 ↔ 2 := Iff.rfl;
  tfae_have 2 ↔ 3 := GL.Hilbert.iff_gentzen;
  tfae_have 2 ↔ 4 := GL.Hilbert.iff_valid_finite;
  tfae_have 2 ↔ 5 := GL.Hilbert.iff_root_forces;
  tfae_finish;

lemma iff_provable_gentzen : A ∈ 𝐆𝐋 ↔ ⊢ᴳ[GL] ∅ ⟹ {A} := provability_TFAE.out 1 3

lemma iff_valid_finite : A ∈ 𝐆𝐋 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A :=
  provability_TFAE.out 1 4

lemma iff_root_forces : A ∈ 𝐆𝐋 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A :=
  provability_TFAE.out 1 5

end Logic.GL

end FFL.ProvabilityLogic

end
