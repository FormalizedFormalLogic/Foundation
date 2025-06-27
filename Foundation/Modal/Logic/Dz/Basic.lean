import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.GL.Independency

namespace LO.Modal

open Formula (atom)
open Logic

protected abbrev Logic.Dz := sumQuasiNormal Logic.GL {∼□⊥, □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)}
instance : Logic.Dz.IsQuasiNormal := inferInstance

instance : Entailment.HasAxiomP Logic.Dz where
  P := by
    constructor;
    apply Logic.sumQuasiNormal.mem₂;
    simp;

lemma Logic.Dz.mem_axiomDz : Logic.Dz ⊢! □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ := by
  apply Logic.subst! (φ := □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
  apply Logic.sumQuasiNormal.mem₂!;
  simp;

instance : Logic.GL ⪱ Logic.Dz := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use ∼□⊥;
    constructor;
    . simp;
    . exact Logic.GL.unprovable_notbox;

section

private inductive Logic.Dz.aux : Logic ℕ
  | mem_GL {φ} : Logic.GL ⊢! φ → Logic.Dz.aux φ
  | axiomP : Logic.Dz.aux (∼□⊥)
  | axiomDz (φ ψ) : Logic.Dz.aux (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ)
  | mdp  {φ ψ} : Logic.Dz.aux (φ ➝ ψ) → Logic.Dz.aux φ → Logic.Dz.aux ψ

private lemma Logic.Dz.eq_aux : Logic.Dz = Logic.Dz.aux := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact Logic.Dz.aux.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | rfl);
      . apply Logic.Dz.aux.axiomP;
      . apply Logic.Dz.aux.axiomDz;
    | mdp _ _ ihφψ ihφ => exact Logic.Dz.aux.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Logic.Dz.aux.mem_GL;
        apply subst!;
        exact h;
      | axiomP => apply Logic.Dz.aux.axiomP;
      | axiomDz _ _ => apply Logic.Dz.aux.axiomDz;
      | mdp _ _ ihφψ ihφ => apply Logic.Dz.aux.mdp ihφψ ihφ;
  . intro h;
    apply iff_provable.mp;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁! h;
    | mdp _ _ ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | axiomDz φ => apply Logic.Dz.mem_axiomDz;
    | axiomP => simp;

-- TODO: Remove `eq_Dz_Dz'`?
protected def Logic.Dz.rec'
  {motive : (φ : Formula ℕ) → (Logic.Dz ⊢! φ) → Prop}
  (mem_GL : ∀ {φ}, (h : Logic.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP : motive (∼□⊥) (by simp))
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Logic.Dz.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : Logic.Dz ⊢! φ ➝ ψ} → {hφ : Logic.Dz ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Logic.Dz ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Logic.Dz.eq_aux.symm ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomDz φ ψ => apply axiomDz;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [←Logic.Dz.eq_aux] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [←Logic.Dz.eq_aux] at hφ;

end

end LO.Modal
