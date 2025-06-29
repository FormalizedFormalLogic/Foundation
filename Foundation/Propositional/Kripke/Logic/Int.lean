import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Kripke.Hilbert
import Foundation.Propositional.Kripke.Filtration
import Foundation.Logic.Disjunctive

namespace LO.Propositional

open Kripke
open Formula.Kripke
open Hilbert.Kripke

@[reducible] protected alias Kripke.FrameClass.Int := FrameClass.all
@[reducible] protected alias Kripke.FrameClass.finite_Int := FrameClass.finite_all


namespace Hilbert.Int.Kripke

instance : Sound Hilbert.Int FrameClass.Int := instSound_of_validates_axioms FrameClass.all.validates_AxiomEFQ

instance : Entailment.Consistent Hilbert.Int := consistent_of_sound_frameclass FrameClass.Int $ by simp

instance : Sound Hilbert.Int FrameClass.finite_Int := instSound_of_validates_axioms FrameClass.finite_all.validates_AxiomEFQ

instance : Canonical Hilbert.Int FrameClass.Int := by tauto;

instance : Complete Hilbert.Int FrameClass.Int := inferInstance

section FFP

instance : Complete Hilbert.Int FrameClass.finite_Int := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.Int);
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFiltrationModel M ↑φ.subformulas;

  apply filtration FM (coarsestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hφ;

  apply Frame.isFinite_iff _ |>.mpr;
  apply FilterEqvQuotient.finite;
  simp;
⟩

end FFP

section DP

variable {M₁ : Kripke.Model} {M₂ : Kripke.Model}

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
  rel_partial_order := {
    refl := by simp [Reflexive];
    trans := by
      simp only [Sum.forall, true_implies, imp_self, implies_true, true_and, false_implies, and_true, and_self, forall_const, imp_false];
      constructor;
      . constructor;
        . intro _ _; apply F₁.trans;
        . intro _ _; apply F₂.trans;
      . constructor;
        . intro _ _ _; apply F₁.trans;
        . intro _ _ _; apply F₂.trans;
    antisymm := by
      simp only [Sum.forall, imp_self, implies_true, reduceCtorEq, and_self, imp_false, false_implies, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
      constructor;
      . intro _ _; apply F₁.antisymm;
      . intro _ _; apply F₂.antisymm;
  }

abbrev counterexampleDPModel (M₁ : Kripke.Model) (M₂ : Kripke.Model) (w₁ : M₁.World) (w₂ : M₂.World) : Model where
  toFrame := counterexampleDPFrame M₁.toFrame M₂.toFrame w₁ w₂;
  Val := ⟨
    λ w a =>
      match w with
      | Sum.inr $ Sum.inl w => M₁ w a
      | Sum.inr $ Sum.inr w => M₂ w a
      | _ => False,
    by
      simp only [counterexampleDPFrame, Sum.forall, imp_false, not_false_eq_true, implies_true, imp_self, IsEmpty.forall_iff, and_self, and_true, true_and];
      constructor;
      . intro _ _;
        apply M₁.Val.hereditary;
      . intro _ _;
        apply M₂.Val.hereditary;
  ⟩

lemma satisfies_left_on_counterexampleDPModel :
  w ⊧ φ ↔ (Satisfies (counterexampleDPModel M₁ M₂ w₁ w₂) (Sum.inr $ Sum.inl w) φ) := by
  induction φ generalizing w with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro hpq X hWX hp;
      obtain ⟨x, hx, ex⟩ : ∃ x, (M₁.Rel w x) ∧ (Sum.inr $ Sum.inl x) = X := by
        replace hWX : (counterexampleDPModel M₁ M₂ w₁ w₂).Rel _ X := hWX;
        simp only [counterexampleDPModel, counterexampleDPFrame] at hWX;
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
        simp only [counterexampleDPModel, counterexampleDPFrame] at hWX;
        split at hWX;
        all_goals simp_all;
      subst ex;
      exact ihq.mp $ h hx $ ihp.mpr hp;
    . intro h v Rwv hp;
      exact ihq.mpr $ h (by simpa) $ ihp.mp hp;
  | _ => simp_all [counterexampleDPModel, Satisfies.iff_models, Satisfies];

theorem disjunctive : Hilbert.Int ⊢! φ ⋎ ψ → Hilbert.Int ⊢! φ ∨ Hilbert.Int ⊢! ψ := by
  contrapose!;
  rintro ⟨hnφ, hnψ⟩;

  obtain ⟨M₁, w₁, hM₁, hφ⟩ := iff_not_validOnFrameClass_exists_model_world.mp $ Complete.exists_countermodel_of_not_provable (𝓜 := FrameClass.Int) hnφ;
  obtain ⟨M₂, w₂, hM₂, hψ⟩ := iff_not_validOnFrameClass_exists_model_world.mp $ Complete.exists_countermodel_of_not_provable (𝓜 := FrameClass.Int) hnψ;

  apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.Int);
  apply not_validOnFrameClass_of_exists_model_world;
  let M := counterexampleDPModel M₁ M₂ w₁ w₂;
  use M, (Sum.inl ());
  constructor;
  . tauto;
  . apply Formula.Kripke.Satisfies.or_def.not.mpr;
    push_neg;
    constructor;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inl w₁) φ ?_;
      . exact satisfies_left_on_counterexampleDPModel.not.mp hφ;
      . apply M₁.refl;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inr w₂) ψ ?_;
      . exact satisfies_right_on_counterexampleDPModel.not.mp hψ;
      . apply M₂.refl;

instance : Entailment.Disjunctive Hilbert.Int := ⟨disjunctive⟩

end DP

end Hilbert.Int.Kripke


propositional_kripke Logic.Int FrameClass.Int
propositional_kripke Logic.Int FrameClass.finite_Int


end LO.Propositional
