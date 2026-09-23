module

public import Foundation.ProvabilityLogic.GL.Basic
public import Foundation.ProvabilityLogic.S.Gentzen.Kripke

/-!
# The logic `S`

## References

- [AB05]
- [KK23]
- [Vis84]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

abbrev Logic.S {α : Type*} : Logic α := 𝐆𝐋 +ᴸ { □A 🡒 A | A }

notation "𝐒" => Logic.S

noncomputable def Formula.rflSubfmls {α : Type*} [DecidableEq α] (A : Formula α) :
    FormulaFinset α :=
  A.subfmls.prebox.image fun B ↦ □B 🡒 B

namespace Logic.S

variable {α : Type*} {A B : Formula α}

lemma mem_of_mem_GL (h : A ∈ 𝐆𝐋) : A ∈ 𝐒 := sumQuasiNormal.mem₁ h

lemma axiomT : □A 🡒 A ∈ 𝐒 := sumQuasiNormal.mem₂ ⟨A, rfl⟩

lemma mdp (h₁ : A 🡒 B ∈ 𝐒) (h₂ : A ∈ 𝐒) : B ∈ 𝐒 := sumQuasiNormal.mdp h₁ h₂

lemma eventually_forces (h : A ∈ 𝐒) {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL]
    {w : ℕ → M.World} (hw : ∀ n, w (n + 1) ≺ w n) : ∃ i, ∀ j ≥ i, w j ⊩[M] A := by
  induction h generalizing κ with
  | mem₁ h => exact ⟨0, fun j _ ↦ GL.Hilbert.sound M h (w j)⟩;
  | mem₂ h =>
    obtain ⟨B, rfl⟩ := h;
    obtain ⟨i, hi⟩ := eventually_isReflexiveOf hw {B};
    exact ⟨i, fun j hj ↦ hi j hj B (by simp)⟩;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨i₁, h₁⟩ := ih₁ M hw;
    obtain ⟨i₂, h₂⟩ := ih₂ M hw;
    exact ⟨max i₁ i₂, fun j hj ↦ h₁ j (by omega) (h₂ j (by omega))⟩;
  | @subst A s _ ih =>
    obtain ⟨i, hi⟩ := ih (M.subst s) hw;
    exact ⟨i, fun j hj ↦ forces_subst.mp (hi j hj)⟩;

variable [DecidableEq α]

lemma mem_of_mem_GL_conj {Γ : FormulaFinset α} (hΓ : ∀ B ∈ Γ, B ∈ 𝐒) :
    ∀ {A}, Γ.conj 🡒 A ∈ 𝐆𝐋 → A ∈ 𝐒 := by
  induction Γ using Finset.induction_on with
  | empty =>
    intro A h;
    have h₁ : ⊢ᴴ[GL] (∅ : FormulaFinset α).conj 🡒 A := h;
    have h₂ : ⊢ᴴ[GL] (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact mem_of_mem_GL (h₁ ⨀ h₂);
  | insert B Γ _ ih =>
    intro A h;
    have h₁ : ⊢ᴴ[GL] (insert B Γ).conj 🡒 A := h;
    have h₂ : ⊢ᴴ[GL] B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    have h₃ : ⊢ᴴ[GL] Γ.conj 🡒 B 🡒 A := by cl_prover [h₁, h₂];
    exact mdp (ih (fun C hC ↦ hΓ C (by simp [hC])) h₃) (hΓ B (by simp));

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

/-- - [KK23, Theorem 3.1]
- [Vis84]
-/
theorem provability_TFAE : [
    A ∈ 𝐒,
    ⊢ᴳ[S] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      ∃ i : ℕ, ∀ j ≥ i, (Sum.inr ↑j : κ ⊕ ℕ∞) ⊩[M.toTail.toModel] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      M.root ⊩[M.toModel] A.rflSubfmls.conj 🡒 A,
    A.rflSubfmls.conj 🡒 A ∈ 𝐆𝐋
  ].TFAE := by
  tfae_have 1 → 3 := fun h _ _ M _ _ hw ↦ eventually_forces h M hw;
  tfae_have 2 ↔ 3 := by simpa [ForcesSequent] using S.Gentzen.iff_eventually_forces (S := ∅ ⟹ {A});
  tfae_have 3 → 4 := fun h _ _ M _ ↦ h M.toTail.toModel (fun n ↦ .inr n)
    (fun n ↦ RootedModel.toTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self));
  tfae_have 4 → 5 := by
    intro h _ _ M _ hΓ;
    obtain ⟨i, hi⟩ := h M;
    have hroot : ∀ B, □B ∈ A.subfmls → M.root ⊩[M.toModel] □B 🡒 B :=
      fun B hB ↦ forces_conj.mp hΓ _
        (Finset.mem_image.mpr ⟨B, FormulaFinset.mem_prebox.mpr hB, rfl⟩);
    exact (RootedModel.toTail.forces_inr_iff (fun _ hB ↦ Formula.subfmls_trans hB) hroot
      Formula.mem_subfmls_self i).mp (hi i le_rfl);
  tfae_have 5 ↔ 6 := GL.iff_root_forces.symm;
  tfae_have 6 → 1 := fun h ↦ mem_of_mem_GL_conj (by simp [Formula.rflSubfmls, axiomT]) h;
  tfae_finish;

lemma iff_gentzen : A ∈ 𝐒 ↔ ⊢ᴳ[S] ∅ ⟹ {A} := provability_TFAE.out 1 2

lemma iff_eventually_forces : A ∈ 𝐒 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] A :=
  provability_TFAE.out 1 3

lemma iff_eventually_forces_tail : A ∈ 𝐒 ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      ∃ i : ℕ, ∀ j ≥ i, (Sum.inr ↑j : κ ⊕ ℕ∞) ⊩[M.toTail.toModel] A :=
  provability_TFAE.out 1 4

lemma iff_mem_GL : A ∈ 𝐒 ↔ A.rflSubfmls.conj 🡒 A ∈ 𝐆𝐋 := provability_TFAE.out 1 6

lemma consistent : ⊥ ∉ (𝐒 : Logic α) := by
  intro h;
  have h : ⊢ᴴ[GL] (⊥ : Formula α).rflSubfmls.conj 🡒 ⊥ := iff_mem_GL.mp h;
  have : (⊥ : Formula α).rflSubfmls = ∅ := by
    ext;
    simp [Formula.rflSubfmls, Formula.subfmls];
  simpa [this, forces_imp] using GL.Hilbert.sound (pointModel (α := α) fun _ ↦ False) h 0;

end Logic.S

end FFL.ProvabilityLogic

end
