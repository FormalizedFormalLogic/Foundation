import Foundation.Modal.Logic.SumQuasiNormal
import Foundation.Modal.Maximal.Unprovability

namespace LO.Modal

open Logic

instance : Modal.GL.IsNormal where

protected abbrev S := sumQuasiNormal Modal.GL {Axioms.T (.atom 0)}
instance : Modal.S.IsQuasiNormal := inferInstance
instance : Entailment.HasAxiomT Modal.S where
  T φ := by
    constructor;
    apply Logic.sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ);
    apply Logic.sumQuasiNormal.mem₂;
    apply Logic.iff_provable.mpr;
    simp;

attribute [grind] Hilbert.Normal.iff_logic_provable_provable Logic.GL.unprovable_AxiomT

instance : Modal.GL ⪱ Modal.S := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . grind;

section

private inductive S' : Logic ℕ
  | mem_GL {φ} : Modal.GL ⊢! φ → Modal.S' φ
  | axiomT (φ) : Modal.S' (Axioms.T φ)
  | mdp  {φ ψ} : Modal.S' (φ ➝ ψ) → Modal.S' φ → Modal.S' ψ

private lemma S'.eq_S : Modal.S' = Modal.S := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem_GL h => apply Logic.sumQuasiNormal.mem₁; exact h;
    | axiomT φ => apply iff_provable.mp; simp;
    | mdp hφψ hφ ihφψ ihφ =>
      apply Logic.sumQuasiNormal.mdp;
      . assumption;
      . assumption;
  . intro h;
    induction h with
    | mem₁ h =>
      apply Modal.S'.mem_GL h;
    | mem₂ h =>
      simp only [iff_provable, Set.mem_singleton_iff] at h;
      subst h;
      exact Modal.S'.axiomT (.atom 0);
    | mdp _ _ ihφψ ihφ =>
      exact Modal.S'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Modal.S'.mem_GL;
        apply subst!;
        exact h;
      | axiomT _ => apply Modal.S'.axiomT;
      | mdp _ _ ihφψ ihφ => apply Modal.S'.mdp ihφψ ihφ;

-- TODO: Remove `eq_S_S'`?
protected def S.rec'
  {motive : (φ : Formula ℕ) → (Modal.S ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Modal.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomT : ∀ {φ}, motive (Axioms.T φ) (by simp))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.S ⊢! φ ➝ ψ} → {hφ : Modal.S ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.S ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Modal.S'.eq_S ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomT h => exact axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [Modal.S'.eq_S] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [Modal.S'.eq_S] at hφ;

end

end LO.Modal
