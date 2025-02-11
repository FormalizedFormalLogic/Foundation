import Foundation.Logic.Disjunctive
import Foundation.IntProp.Kripke.Hilbert.Int.Basic

namespace LO.IntProp

open Kripke
open Entailment
open Formula Formula.Kripke

namespace Hilbert.Int

variable {φ ψ : Formula ℕ}

abbrev counterexampleDPFrame (F₁ : Kripke.Frame) (F₂ : Kripke.Frame) (w₁ : F₁.World) (w₂ : F₂.World) : Kripke.Frame where
  World := Unit ⊕ F₁.World ⊕ F₂.World;
  Rel x y :=
    match x, y with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl y) => F₁.Rel w₁ y
    | (Sum.inl _), (Sum.inr $ Sum.inr y) => F₂.Rel w₂ y
    | (Sum.inr $ Sum.inl x), (Sum.inr $ Sum.inl y) => F₁.Rel x y
    | (Sum.inr $ Sum.inr x), (Sum.inr $ Sum.inr y) => F₂.Rel x y
    | _, _ => False
  rel_refl := by simp [Reflexive];
  rel_trans := by
    unfold Transitive;
    simp only [Sum.forall, true_implies, imp_self, implies_true, true_and, false_implies, and_true, and_self, forall_const, imp_false];
    constructor;
    . constructor;
      . intro _ _; apply F₁.rel_trans;
      . intro _ _; apply F₂.rel_trans;
    . constructor;
      . intro _ _ _; apply F₁.rel_trans;
      . intro _ _ _; apply F₂.rel_trans;
  /-
  rel_antisymm := by
    simp only [Sum.forall, imp_self, implies_true, reduceCtorEq, and_self, imp_false, false_implies, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
    constructor;
    . intro _ _; apply F₁.rel_antisymm;
    . intro _ _; apply F₂.rel_antisymm;
  -/

abbrev counterexampleDPModel (M₁ : Kripke.Model) (M₂ : Kripke.Model) (w₁ : M₁.World) (w₂ : M₂.World) : Model where
  toFrame := counterexampleDPFrame M₁.toFrame M₂.toFrame w₁ w₂;
  Val := ⟨
    λ w a =>
      match w with
      | Sum.inr $ Sum.inl w => M₁ w a
      | Sum.inr $ Sum.inr w => M₂ w a
      | _ => False,
    by
      simp only [Sum.forall, imp_false, not_false_eq_true, implies_true, imp_self, IsEmpty.forall_iff, and_self, and_true, true_and];
      constructor;
      . intro _ _;
        apply M₁.Val.hereditary;
      . intro _ _;
        apply M₂.Val.hereditary;
  ⟩

variable {M₁ : Kripke.Model} {M₂ : Kripke.Model}

lemma satisfies_left_on_counterexampleDPModel :
  w ⊧ φ ↔ (Satisfies (counterexampleDPModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inl w) φ) := by
  induction φ using rec' generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro hpq X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₁.Rel w x) ∧ (Sum.inr $ Sum.inl x) = X := by
        replace hWX : (counterexampleDPModel M₁ M₂ w₁ w₂).Rel _ X := hWX;
        simp [counterexampleDPModel] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ hpq hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      apply @ihq v |>.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [counterexampleDPModel, Satisfies.iff_models, Satisfies];

lemma satisfies_right_on_counterexampleDPModel :
  w ⊧ φ ↔ (Satisfies (counterexampleDPModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inr w) φ) := by
  induction φ using rec' generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₂.Rel w x) ∧ (Sum.inr $ Sum.inr x) = X := by
        replace hWX : (counterexampleDPModel M₁ M₂ w₁ w₂).Rel _ X := hWX;
        simp [counterexampleDPModel] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      exact ihq.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [counterexampleDPModel, Satisfies.iff_models, Satisfies];

theorem disjunctive : (Hilbert.Int) ⊢! φ ⋎ ψ → (Hilbert.Int) ⊢! φ ∨ (Hilbert.Int) ⊢! ψ := by
  contrapose;
  intro hC; push_neg at hC;
  have ⟨hnφ, hnψ⟩ := hC;
  obtain ⟨F₁, V₁, w₁, hφ⟩ := by simpa [ValidOnFrame, ValidOnModel] using not_imp_not.mpr Int.Kripke.complete.complete hnφ;
  obtain ⟨F₂, V₂, w₂, hψ⟩ := by simpa [ValidOnFrame, ValidOnModel] using not_imp_not.mpr Int.Kripke.complete.complete hnψ;
  apply (not_imp_not.mpr Int.Kripke.sound.sound);
  apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
  let M := counterexampleDPModel ⟨F₁, V₁⟩ ⟨F₂, V₂⟩ w₁ w₂;
  use M, (Sum.inl ());
  constructor;
  . tauto;
  . apply Formula.Kripke.Satisfies.or_def.not.mpr;
    push_neg;
    constructor;
    . have := not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inl w₁) φ (by aesop);
      apply this;
      exact satisfies_left_on_counterexampleDPModel.not.mp hφ;
    . have := not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inr w₂) ψ (by aesop);
      apply this;
      exact satisfies_right_on_counterexampleDPModel.not.mp hψ;

instance : Disjunctive (Hilbert.Int) := ⟨disjunctive⟩

end Hilbert.Int

end LO.IntProp
