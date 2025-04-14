import Foundation.Modal.Logic.Extension
import Foundation.ProvabilityLogic.GL.Completeness

namespace LO.Modal

open Logic

protected abbrev Logic.S := addQuasiNormal Logic.GL (Axioms.T (.atom 0))
instance : Logic.S.QuasiNormal where
  subset_K := by
    intro φ hφ;
    apply Logic.sumQuasiNormal.mem₁;
    exact Logic.of_mem_K hφ;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    apply Logic.sumQuasiNormal.mdp hφψ hφ;
  subst_closed := by
    intro φ hφ s;
    apply Logic.sumQuasiNormal.subst;
    exact hφ;

lemma Logic.S.mem_axiomT : □φ ➝ φ ∈ Logic.S := by
  apply Logic.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ);
  apply Logic.sumQuasiNormal.mem₂;
  tauto;


lemma Logic.GL_subset_S : Logic.GL ⊆ Logic.S := by
  intro φ hφ;
  apply Logic.sumQuasiNormal.mem₁;
  assumption;

lemma Logic.GL_ssubset_S : Logic.GL ⊂ Logic.S := by
  constructor;
  . exact Logic.GL_subset_S;
  . suffices ∃ φ, φ ∈ Logic.S ∧ φ ∉ Logic.GL by exact Set.not_subset.mpr this;
    use (Axioms.T (.atom 0));
    constructor;
    . exact Logic.S.mem_axiomT;
    . exact Hilbert.GL.unprovable_AxiomT;
instance : ProperSublogic Logic.GL Logic.S := ⟨Logic.GL_ssubset_S⟩


section

private inductive Logic.S' : Logic
  | mem_GL {φ} : φ ∈ Logic.GL → Logic.S' φ
  | axiomT (φ) : Logic.S' (Axioms.T φ)
  | mdp  {φ ψ} : Logic.S' (φ ➝ ψ) → Logic.S' φ → Logic.S' ψ

private lemma Logic.eq_S_S' : Logic.S = Logic.S' := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact Logic.S'.mem_GL h;
    | mem₂ h => subst h; exact Logic.S'.axiomT (.atom 0);
    | mdp _ _ ihφψ ihφ => exact Logic.S'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Logic.S'.mem_GL;
        exact Logic.subst h;
      | axiomT _ => apply Logic.S'.axiomT;
      | mdp _ _ ihφψ ihφ =>
        apply Logic.S'.mdp ihφψ ihφ;
  . intro h;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | axiomT φ =>
      exact sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ) $ by
        apply Logic.sumQuasiNormal.mem₂;
        simp;

-- TODO: Remove `eq_S_S'`?
protected def Logic.S.rec'
  {motive : (φ : Formula ℕ) → φ ∈ Logic.S → Prop}
  (mem_GL : ∀ {φ}, (h : φ ∈ Logic.GL) → motive φ (sumQuasiNormal.mem₁ h))
  (axiomT : ∀ {φ}, motive (Axioms.T φ) (sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ) (sumQuasiNormal.mem₂ (by tauto))))
  (mdp : ∀ {φ ψ}, {hφψ : φ ➝ ψ ∈ Logic.S} → {hφ : φ ∈ Logic.S} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (sumQuasiNormal.mdp hφψ hφ))
  : ∀ {φ}, (h : φ ∈ Logic.S) → motive φ h := by
  intro φ h;
  rw [Logic.eq_S_S'] at h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomT h => exact axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_S_S'] at hφψ;
    . rwa [←Logic.eq_S_S'] at hφ;

end

end LO.Modal
