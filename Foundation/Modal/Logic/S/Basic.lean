import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability

namespace LO.Modal

open Logic

protected abbrev Logic.S := addQuasiNormal Logic.GL (Axioms.T (.atom 0))
instance : Logic.S.IsQuasiNormal := inferInstance
instance : Entailment.HasAxiomT Logic.S where
  T φ := by
    constructor;
    apply Logic.sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ);
    apply Logic.sumQuasiNormal.mem₂;
    simp;

instance : Logic.GL ⪱ Logic.S := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . exact Logic.GL.unprovable_AxiomT;

section

/-
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
-/

-- TODO: Remove `eq_S_S'`?
protected def Logic.S.rec'
  {motive : (φ : Formula ℕ) → (Logic.S ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Logic.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomT : ∀ {φ}, motive (Axioms.T φ) (by simp))
  (mdp : ∀ {φ ψ}, {hφψ : Logic.S ⊢! φ ➝ ψ} → {hφ : Logic.S ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (sumQuasiNormal.mdp! hφψ hφ))
  : ∀ {φ}, (h : Logic.S ⊢! φ) → motive φ h := by
  intro φ h;
  induction (iff_provable.mp h) with
  | mem₁ h₁ => apply mem_GL; assumption;
  | mem₂ h₂ =>
    replace h₂ := iff_provable.mp h₂; subst h₂;
    apply axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . apply iff_provable.mpr; exact hφψ;
    . apply iff_provable.mpr; exact hφ;
  | @subst φ s hφ ihφ =>
    generalize φ⟦s⟧ = ψ at h ⊢;
    sorry;

  /-
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomT h => exact axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_S_S'] at hφψ;
    . rwa [←Logic.eq_S_S'] at hφ;
-/

end

end LO.Modal
