module

public import Foundation.Propositional.Kripke.Hilbert.Int.Basic

@[expose] public section

namespace LO.Propositional.Hilbert.Int

open Kripke
open Formula.Kripke

variable {M₁ : Kripke.Model} {M₂ : Kripke.Model} {φ ψ : Formula ℕ}

abbrev counterexampleDPModel (M₁ : Kripke.Model) (M₂ : Kripke.Model) (w₁ : M₁.World) (w₂ : M₂.World) : Kripke.Model where
  World := Unit ⊕ M₁.World ⊕ M₂.World;
  Rel x y :=
    match x, y with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl y) => M₁.Rel w₁ y
    | (Sum.inl _), (Sum.inr $ Sum.inr y) => M₂.Rel w₂ y
    | (Sum.inr $ Sum.inl x), (Sum.inr $ Sum.inl y) => M₁.Rel x y
    | (Sum.inr $ Sum.inr x), (Sum.inr $ Sum.inr y) => M₂.Rel x y
    | _, _ => False
  rel_partial_order := {
    refl := by simp only [Sum.forall, implies_true, Frame.refl, and_self];
    trans := by
      simp only [Sum.forall, imp_self, implies_true, true_and, false_implies, and_true, and_self, forall_const, imp_false];
      constructor;
      . constructor;
        . intro _ _; apply M₁.trans;
        . intro _ _; apply M₂.trans;
      . constructor;
        . intro _ _ _; apply M₁.trans;
        . intro _ _ _; apply M₂.trans;
    antisymm := by
      simp only [Sum.forall, imp_self, implies_true, reduceCtorEq, and_self, imp_false, false_implies, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
      constructor;
      . intro _ _; apply M₁.antisymm;
      . intro _ _; apply M₂.antisymm;
  }
  Val := ⟨
    λ a w =>
      match w with
      | Sum.inr $ Sum.inl w => M₁ a w
      | Sum.inr $ Sum.inr w => M₂ a w
      | Sum.inl _ => False
    ,
    by
      intro x y Rxy a;
      match x, y with
      | (Sum.inl _), _ => tauto;
      | (Sum.inr $ Sum.inl x), (Sum.inr $ Sum.inl y) => apply M₁.Val.hereditary Rxy;
      | (Sum.inr $ Sum.inr x), (Sum.inr $ Sum.inr y) => apply M₂.Val.hereditary Rxy;
  ⟩

lemma satisfies_left_on_counterexampleDPModel :
  w ⊧ φ ↔ (Satisfies (counterexampleDPModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inl w) φ) := by
  induction φ generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro hpq X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₁.Rel w x) ∧ (Sum.inr $ Sum.inl x) = X := by
        replace hWX : (counterexampleDPModel M₁ M₂ w₁ w₂).Rel _ X := hWX;
        dsimp only [counterexampleDPModel] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ hpq hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      apply @ihq v |>.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [counterexampleDPModel, Satisfies.iff_models, Satisfies];

lemma satisfies_right_on_counterexampleDPModel :
  w ⊧ φ ↔ (Satisfies (counterexampleDPModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inr w) φ) := by
  induction φ generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₂.Rel w x) ∧ (Sum.inr $ Sum.inr x) = X := by
        replace hWX : (counterexampleDPModel M₁ M₂ w₁ w₂).Rel _ X := hWX;
        dsimp only [counterexampleDPModel] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      exact ihq.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [counterexampleDPModel, Satisfies.iff_models, Satisfies];

theorem disjunctive : Hilbert.Int ⊢ φ ⋎ ψ → Hilbert.Int ⊢ φ ∨ Hilbert.Int ⊢ ψ := by
  contrapose!;
  rintro ⟨hnφ, hnψ⟩;

  obtain ⟨M₁, w₁, hM₁, hφ⟩ := iff_not_validOnFrameClass_exists_model_world.mp $ instKripkeComplete.exists_countermodel_of_not_provable hnφ;
  obtain ⟨M₂, w₂, hM₂, hψ⟩ := iff_not_validOnFrameClass_exists_model_world.mp $ instKripkeComplete.exists_countermodel_of_not_provable hnψ;

  apply soundKripke.not_provable_of_countermodel;
  apply not_validOnFrameClass_of_exists_model_world;
  let M := counterexampleDPModel M₁ M₂ w₁ w₂;
  use M, (Sum.inl ());
  constructor;
  . tauto;
  . apply Formula.Kripke.Satisfies.or_def.not.mpr;
    push Not;
    constructor;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inl w₁) φ ?_;
      . exact satisfies_left_on_counterexampleDPModel.not.mp hφ;
      . apply M₁.refl;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inr w₂) ψ ?_;
      . exact satisfies_right_on_counterexampleDPModel.not.mp hψ;
      . apply M₂.refl;

end LO.Propositional.Hilbert.Int

end
