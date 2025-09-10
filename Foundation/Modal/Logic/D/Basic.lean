import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.GL.Independency
import Foundation.Modal.Logic.S.Basic
import Foundation.Modal.Entailment.GL

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

lemma D.mem_axiomDz : Modal.D ⊢! □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ := by
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
    | axiomD φ => apply Modal.D.mem_axiomDz;
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
  {motive  : (φ : Formula ℕ) → (Modal.D ⊢! φ) → Prop}
  (mem_GL  : ∀ {φ}, (h : Modal.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP  : motive (∼□⊥) (by simp))
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Modal.D.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.D ⊢! φ ➝ ψ} → {hφ : Modal.D ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.D ⊢! φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Modal.D'.eq_D ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomD φ ψ => apply axiomDz;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [D'.eq_D] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [D'.eq_D] at hφ;

end


section

attribute [-simp] Logic.iff_provable
open LO.Entailment LO.Modal.Entailment

instance : Modal.D ⪯ Modal.S := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ using D.rec' with
  | mem_GL h => exact WeakerThan.pbl h;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ => exact axiomT!;

instance : Entailment.GL Modal.GL where
  L _ := by
    constructor;
    apply Logic.iff_provable.mp;
    apply Hilbert.Normal.iff_logic_provable_provable.mpr;
    simp;

@[simp]
lemma GL.box_disj_Tc {l : List (Formula ℕ)} : Modal.GL ⊢! l.box.disj ➝ □l.box.disj := by
  apply left_Disj!_intro;
  intro ψ hψ;
  obtain ⟨ψ, hψ, rfl⟩ := List.exists_box_of_mem_box hψ;
  apply C!_trans axiomFour!;
  apply axiomK'!;
  apply nec!;
  apply right_Disj!_intro;
  assumption;

lemma D.ldisj_axiomDz {l : List (Formula ℕ)} : Modal.D ⊢! □(l.box.disj) ➝ l.box.disj := by
  induction l with
  | nil => exact axiomP!;
  | cons φ l ih =>
    apply C!_replace ?_ ?_ (D.mem_axiomDz (φ := φ) (ψ := l.box.disj));
    . apply sumQuasiNormal.mem₁!;
      apply axiomK'!;
      apply nec!;
      suffices Modal.GL ⊢! □φ ⋎ l.box.disj ➝ □φ ⋎ □l.box.disj by simpa;
      have : Modal.GL ⊢! l.box.disj ➝ □l.box.disj := GL.box_disj_Tc;
      cl_prover [this];
    . suffices Modal.D ⊢! □φ ⋎ □l.box.disj ➝ □φ ⋎ l.box.disj by simpa;
      cl_prover [ih];

lemma D.fdisj_axiomDz {s : Finset (Formula ℕ)} : Modal.D ⊢! □(s.box.disj) ➝ s.box.disj := by
  apply C!_replace ?_ ?_ $ D.ldisj_axiomDz (l := s.toList);
  . apply sumQuasiNormal.mem₁!;
    apply axiomK'!;
    apply nec!;
    apply left_Fdisj!_intro;
    rintro ψ hψ;
    apply right_Disj!_intro;
    obtain ⟨ψ, hψ, rfl⟩ : ∃ a ∈ s, □a = ψ := by simpa using hψ;
    apply List.box_mem_of;
    simpa;
  . apply left_Disj!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    obtain ⟨ψ, hψ₂, rfl⟩ := List.exists_box_of_mem_box hψ;
    simpa using hψ₂;

end

end LO.Modal
