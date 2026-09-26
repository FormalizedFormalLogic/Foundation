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

variable {α : Type*} {A : Formula α}

lemma of_GL (h : 𝐆𝐋 ⊢ A) : 𝐒 ⊢ A := sumQuasiNormal.of_left h

lemma axiomT : 𝐒 ⊢ □A 🡒 A := sumQuasiNormal.mem₂ ⟨A, rfl⟩

lemma eventually_forces (h : 𝐒 ⊢ A) {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL]
    {w : ℕ → M.World} (hw : ∀ n, w (n + 1) ≺ w n) : ∃ i, ∀ j ≥ i, w j ⊩[_] A := by
  induction h generalizing κ with
  | mem₁ h => exact ⟨0, fun j _ ↦ GL.sound M h (w j)⟩;
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

section

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

/-- - [KK23, Theorem 3.1]
- [Vis84]
-/
theorem provability_TFAE : [
    𝐒 ⊢ A,
    ⊢ᴳ[𝐒] ∅ ⟹[1] {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[M] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      ∃ i : ℕ, ∀ j ≥ i, (Sum.inr ↑j : M.toTail.World) ⊩[M.toTail.toModel] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      M.root ⊩[M.toModel] A.rflSubfmls.conj 🡒 A,
    𝐆𝐋 ⊢ A.rflSubfmls.conj 🡒 A
  ].TFAE := by
  tfae_have 1 → 3 := fun h _ _ M _ _ hw ↦ eventually_forces h M hw;
  tfae_have 2 ↔ 3 := by
    simpa [ForcesSequent] using S.Gentzen.iff_eventually_forces (Γ := ∅) (Δ := {A});
  tfae_have 3 → 4 := fun h _ _ M _ ↦ h M.toTail.toModel (fun n ↦ .inr n)
    (fun n ↦ Model.toFreeTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self));
  tfae_have 4 → 5 := by
    intro h _ _ M _ hΓ;
    obtain ⟨i, hi⟩ := h M;
    have hroot : ∀ B, □B ∈ A.subfmls → M.root ⊩[_] □B 🡒 B :=
      fun B hB ↦ forces_conj.mp hΓ _
        (Finset.mem_image.mpr ⟨B, FormulaFinset.mem_prebox.mpr hB, rfl⟩);
    exact (Model.toFreeTail.forces_inr_iff (fun _ ↦ rfl) (fun _ hB ↦ Formula.subfmls_trans hB) hroot
      Formula.mem_subfmls_self i).mp (hi i le_rfl);
  tfae_have 5 ↔ 6 := GL.iff_root_forces.symm;
  tfae_have 6 → 1 := GL.sumQuasiNormal_of_conj (by simp [Formula.rflSubfmls, axiomT]);
  tfae_finish;

lemma iff_provable_gentzen : 𝐒 ⊢ A ↔ ⊢ᴳ[𝐒] ∅ ⟹[1] {A} := provability_TFAE.out 1 2

omit [DecidableEq α] in
lemma iff_eventually_forces : 𝐒 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩[_] A := by
  classical
  exact provability_TFAE.out 1 3

omit [DecidableEq α] in
lemma iff_eventually_forces_tail : 𝐒 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      ∃ i : ℕ, ∀ j ≥ i, (Sum.inr ↑j : M.toTail.World) ⊩[M.toTail.toModel] A := by
  classical
  exact provability_TFAE.out 1 4

lemma iff_provable_GL : 𝐒 ⊢ A ↔ 𝐆𝐋 ⊢ A.rflSubfmls.conj 🡒 A := provability_TFAE.out 1 6

/-- A formula outside `𝐒` is refuted at the root of a finite GL-model that is reflexive at the
root for its boxed subformulas. -/
lemma exists_countermodel (h : 𝐒 ⊬ A) :
    ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
      M.root ⊮[_] A ∧
      ∀ B, □B ∈ A.subfmls → M.root ⊩[_] □B 🡒 B := by
  obtain ⟨κ, _, M, _, hM⟩ :
      ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
        M.root ⊮[_] A.rflSubfmls.conj 🡒 A := by
    simpa using GL.iff_root_forces.not.mp (iff_provable_GL.not.mp h);
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hM;
  exact ⟨κ, inferInstance, M, inferInstance, h₂,
    fun B hB ↦ forces_conj.mp h₁ _ (Finset.mem_image.mpr ⟨B, by simpa using hB, rfl⟩)⟩;

end

instance : Entailment.Consistent (𝐒 : Logic α) := by
  classical
  apply consistent_iff_exists_unprovable.mpr;
  use ⊥;
  by_contra! h;
  replace h := iff_provable_GL.mp h;
  have : (⊥ : Formula α).rflSubfmls = ∅ := by
    ext;
    simp [Formula.rflSubfmls, Formula.subfmls];
  simpa [this, forces_imp] using GL.sound (pointModel (α := α) fun _ ↦ False) h 0;

end Logic.S

end FFL.ProvabilityLogic

end
