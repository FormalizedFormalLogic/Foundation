import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.GL.Independency
import Foundation.Modal.Logic.S.Basic

namespace LO.Modal

open Formula (atom)
open Logic

protected abbrev D := sumQuasiNormal Modal.GL {∼□⊥, □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)}
instance : Modal.D.IsQuasiNormal := inferInstance

instance : Entailment.HasAxiomP Modal.D where
  P := by
    constructor;
    apply Logic.sumQuasiNormal.mem₂;
    simp;

lemma D.mem_axiomD : Modal.D ⊢! □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ := by
  apply Logic.subst! (φ := □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
  apply Logic.sumQuasiNormal.mem₂!;
  simp;

instance : Modal.GL ⪱ Modal.D := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use ∼□⊥;
    constructor;
    . simp;
    . simpa using GL.unprovable_notbox;

section

private inductive D' : Logic ℕ
  | mem_GL {φ} : Modal.GL ⊢! φ → Modal.D' φ
  | axiomP : Modal.D' (∼□⊥)
  | axiomD (φ ψ) : Modal.D' (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ)
  | mdp  {φ ψ} : Modal.D' (φ ➝ ψ) → Modal.D' φ → Modal.D' ψ

private lemma D'.eq_D : Modal.D' = Modal.D := by
  ext φ;
  constructor;
  . intro h;
    apply iff_provable.mp;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁! h;
    | mdp _ _ ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | axiomD φ => apply Modal.D.mem_axiomD;
    | axiomP => simp;
  . intro h;
    induction h with
    | mem₁ h => exact Modal.D'.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | rfl);
      . apply Modal.D'.axiomP;
      . apply Modal.D'.axiomD;
    | mdp _ _ ihφψ ihφ => exact Modal.D'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Modal.D'.mem_GL;
        apply subst!;
        exact h;
      | axiomP => apply Modal.D'.axiomP;
      | axiomD _ _ => apply Modal.D'.axiomD;
      | mdp _ _ ihφψ ihφ => apply Modal.D'.mdp ihφψ ihφ;

-- TODO: Remove `eq_D_D'`?
protected def D.rec'
  {motive : (φ : Formula ℕ) → (Modal.D ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Modal.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP : motive (∼□⊥) (by simp))
  (axiomD : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Modal.D.mem_axiomD))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.D ⊢! φ ➝ ψ} → {hφ : Modal.D ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.D ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Modal.D'.eq_D ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomD φ ψ => apply axiomD;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [D'.eq_D] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [D'.eq_D] at hφ;

open LO.Entailment LO.Modal.Entailment in
instance : Modal.D ⪯ Modal.S := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ using D.rec' with
  | mem_GL h => exact WeakerThan.pbl h;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ => exact axiomT!;

end

end LO.Modal
