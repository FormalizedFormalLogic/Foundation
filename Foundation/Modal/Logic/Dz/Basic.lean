import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.GL.Independency

namespace LO.Modal

open Formula (atom)
open Logic

protected abbrev Dz := sumQuasiNormal Modal.GL {∼□⊥, □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)}
instance : Modal.Dz.IsQuasiNormal := inferInstance

instance : Entailment.HasAxiomP Modal.Dz where
  P := by
    constructor;
    apply Logic.sumQuasiNormal.mem₂;
    simp;

lemma Dz.mem_axiomDz : Modal.Dz ⊢! □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ := by
  apply Logic.subst! (φ := □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
  apply Logic.sumQuasiNormal.mem₂!;
  simp;

instance : Modal.GL ⪱ Modal.Dz := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use ∼□⊥;
    constructor;
    . simp;
    . simpa using GL.unprovable_notbox;

section

private inductive Dz' : Logic ℕ
  | mem_GL {φ} : Modal.GL ⊢! φ → Modal.Dz' φ
  | axiomP : Modal.Dz' (∼□⊥)
  | axiomDz (φ ψ) : Modal.Dz' (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ)
  | mdp  {φ ψ} : Modal.Dz' (φ ➝ ψ) → Modal.Dz' φ → Modal.Dz' ψ

private lemma Dz'.eq_Dz : Modal.Dz' = Modal.Dz := by
  ext φ;
  constructor;
  . intro h;
    apply iff_provable.mp;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁! h;
    | mdp _ _ ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | axiomDz φ => apply Modal.Dz.mem_axiomDz;
    | axiomP => simp;
  . intro h;
    induction h with
    | mem₁ h => exact Modal.Dz'.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | rfl);
      . apply Modal.Dz'.axiomP;
      . apply Modal.Dz'.axiomDz;
    | mdp _ _ ihφψ ihφ => exact Modal.Dz'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Modal.Dz'.mem_GL;
        apply subst!;
        exact h;
      | axiomP => apply Modal.Dz'.axiomP;
      | axiomDz _ _ => apply Modal.Dz'.axiomDz;
      | mdp _ _ ihφψ ihφ => apply Modal.Dz'.mdp ihφψ ihφ;

-- TODO: Remove `eq_Dz_Dz'`?
protected def Dz.rec'
  {motive : (φ : Formula ℕ) → (Modal.Dz ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Modal.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP : motive (∼□⊥) (by simp))
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Modal.Dz.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.Dz ⊢! φ ➝ ψ} → {hφ : Modal.Dz ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.Dz ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Modal.Dz'.eq_Dz ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomDz φ ψ => apply axiomDz;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [Dz'.eq_Dz] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [Dz'.eq_Dz] at hφ;

end

end LO.Modal
