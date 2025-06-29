import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability

namespace LO.Modal

open Logic

protected abbrev Logic.S := sumQuasiNormal Logic.GL {Axioms.T (.atom 0)}
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

private inductive Logic.S.aux : Logic ℕ
  | mem_GL {φ} : Logic.GL ⊢! φ → Logic.S.aux φ
  | axiomT (φ) : Logic.S.aux (Axioms.T φ)
  | mdp  {φ ψ} : Logic.S.aux (φ ➝ ψ) → Logic.S.aux φ → Logic.S.aux ψ

private lemma Logic.S.eq_aux : Logic.S = Logic.S.aux := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h =>
      apply Logic.S.aux.mem_GL h;
    | mem₂ h =>
      simp only [iff_provable, Set.mem_singleton_iff] at h;
      subst h;
      exact Logic.S.aux.axiomT (.atom 0);
    | mdp _ _ ihφψ ihφ =>
      exact Logic.S.aux.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Logic.S.aux.mem_GL;
        apply subst!;
        exact h;
      | axiomT _ => apply Logic.S.aux.axiomT;
      | mdp _ _ ihφψ ihφ => apply Logic.S.aux.mdp ihφψ ihφ;
  . intro h;
    induction h with
    | mem_GL h => apply Logic.sumQuasiNormal.mem₁; exact h;
    | axiomT φ => apply iff_provable.mp; simp;
    | mdp hφψ hφ ihφψ ihφ =>
      apply Logic.sumQuasiNormal.mdp;
      . assumption;
      . assumption;

-- TODO: Remove `eq_S_S'`?
protected def Logic.S.rec'
  {motive : (φ : Formula ℕ) → (Logic.S ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Logic.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomT : ∀ {φ}, motive (Axioms.T φ) (by simp))
  (mdp : ∀ {φ ψ}, {hφψ : Logic.S ⊢! φ ➝ ψ} → {hφ : Logic.S ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Logic.S ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Logic.S.eq_aux.symm ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomT h => exact axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [←Logic.S.eq_aux] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [←Logic.S.eq_aux] at hφ;

end

end LO.Modal
