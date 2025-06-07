import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.GL.Independency

namespace LO.Modal

open Logic

protected abbrev Logic.Dz := sumQuasiNormal Logic.GL {∼□⊥, □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)}
instance : Logic.Dz.IsQuasiNormal where
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

lemma Logic.Dz.mem_axiomP : ∼□⊥ ∈ Logic.Dz := by
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

lemma Logic.Dz.mem_axiomDz : □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ ∈ Logic.Dz := by
  apply Logic.subst (φ := □(□(.atom 0) ⋎ □(.atom 1)) ➝ □(.atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

lemma Logic.GL_subset_Dz : Logic.GL ⊆ Logic.Dz := by
  intro φ hφ;
  apply Logic.sumQuasiNormal.mem₁;
  assumption;

lemma Logic.GL_ssubset_Dz : Logic.GL ⊂ Logic.Dz := by
  constructor;
  . exact Logic.GL_subset_Dz;
  . suffices ∃ φ, φ ∈ Logic.Dz ∧ φ ∉ Logic.GL by exact Set.not_subset.mpr this;
    use ∼□⊥;
    constructor;
    . exact Logic.Dz.mem_axiomP
    . exact Logic.GL.unprovable_notbox;


section

private inductive Logic.Dz' : Logic
  | mem_GL {φ} : φ ∈ Logic.GL → Logic.Dz' φ
  | axiomP : Logic.Dz' (∼□⊥)
  | axiomDz (φ ψ) : Logic.Dz' (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ)
  | mdp  {φ ψ} : Logic.Dz' (φ ➝ ψ) → Logic.Dz' φ → Logic.Dz' ψ

private lemma Logic.eq_Dz_Dz' : Logic.Dz = Logic.Dz' := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact Logic.Dz'.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | rfl);
      . apply Logic.Dz'.axiomP;
      . apply Logic.Dz'.axiomDz;
    | mdp _ _ ihφψ ihφ => exact Logic.Dz'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h => apply Logic.Dz'.mem_GL; exact Logic.subst h;
      | axiomP => apply Logic.Dz'.axiomP;
      | axiomDz _ _ => apply Logic.Dz'.axiomDz;
      | mdp _ _ ihφψ ihφ => apply Logic.Dz'.mdp ihφψ ihφ;
  . intro h;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | axiomDz φ => apply Logic.Dz.mem_axiomDz;
    | axiomP => apply Logic.Dz.mem_axiomP;

-- TODO: Remove `eq_S_Dz'`?
protected def Logic.Dz.rec'
  {motive : (φ : Formula ℕ) → φ ∈ Logic.Dz → Prop}
  (mem_GL : ∀ {φ}, (h : φ ∈ Logic.GL) → motive φ (sumQuasiNormal.mem₁ h))
  (axiomP : motive (∼□⊥) Logic.Dz.mem_axiomP)
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Logic.Dz.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : φ ➝ ψ ∈ Logic.Dz} → {hφ : φ ∈ Logic.Dz} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (sumQuasiNormal.mdp hφψ hφ))
  : ∀ {φ}, (h : φ ∈ Logic.Dz) → motive φ h := by
  intro φ h;
  rw [Logic.eq_Dz_Dz'] at h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomDz φ ψ => apply axiomDz;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_Dz_Dz'] at hφψ;
    . rwa [←Logic.eq_Dz_Dz'] at hφ;

end

end LO.Modal
