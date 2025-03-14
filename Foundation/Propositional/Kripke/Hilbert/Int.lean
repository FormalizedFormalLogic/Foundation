import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration
import Foundation.Logic.Disjunctive

namespace LO.Propositional

open Formula.Kripke
open Hilbert.Kripke

open Kripke

namespace Hilbert.Int.Kripke

protected instance sound : Sound Hilbert.Int FrameClass.all :=
  instSound_of_validates_axioms FrameClass.all.validates_AxiomEFQ

protected instance consistent : Entailment.Consistent Hilbert.Int := consistent_of_sound_frameclass FrameClass.all (by simp)

instance sound_finite : Sound Hilbert.Int FrameClass.finite_all :=
  instSound_of_validates_axioms FrameClass.finite_all.validates_AxiomEFQ

instance canonical : Canonical Hilbert.Int FrameClass.all := by tauto;

instance complete: Complete Hilbert.Int FrameClass.all := inferInstance


section FFP

instance complete_finite : Complete (Hilbert.Int) FrameClass.finite_all := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;

  apply filteration FM (coarsestFilterationModel.filterOf) (by simp) |>.mpr;
  apply hφ;
  apply Frame.isFinite_iff _ |>.mpr
  apply FilterEqvQuotient.finite;
  simp;
⟩

end FFP


section DP

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
  rel_antisymm := by
    unfold AntiSymmetric;
    simp only [Sum.forall, imp_self, implies_true, reduceCtorEq, and_self, imp_false, false_implies, Sum.inr.injEq, true_and, Sum.inl.injEq, and_true];
    constructor;
    . intro _ _; apply F₁.rel_antisymm;
    . intro _ _; apply F₂.rel_antisymm;

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
  induction φ using Formula.rec' generalizing w with
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
  induction φ using Formula.rec' generalizing w with
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

  replace hnφ := Semantics.set_models_iff.not.mp $ (not_imp_not.mpr Int.Kripke.complete.complete) hnφ;
  push_neg at hnφ;
  obtain ⟨F₁, _, hF₁⟩ := hnφ;
  obtain ⟨V₁, w₁, hφ⟩ := Formula.Kripke.ValidOnFrame.exists_valuation_world_of_not hF₁;

  replace hnψ := Semantics.set_models_iff.not.mp $ (not_imp_not.mpr Int.Kripke.complete.complete) hnψ;
  push_neg at hnψ;
  obtain ⟨F₂, _, hF₂⟩ := hnψ;
  obtain ⟨V₂, w₂, hψ⟩ := Formula.Kripke.ValidOnFrame.exists_valuation_world_of_not hF₂;

  apply (not_imp_not.mpr Int.Kripke.sound.sound);
  apply not_validOnFrameClass_of_exists_model_world;
  let M := counterexampleDPModel ⟨F₁, V₁⟩ ⟨F₂, V₂⟩ w₁ w₂;
  use M, (Sum.inl ());
  constructor;
  . tauto;
  . apply Formula.Kripke.Satisfies.or_def.not.mpr;
    push_neg;
    constructor;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inl w₁) φ (by aesop);
      exact satisfies_left_on_counterexampleDPModel.not.mp hφ;
    . apply not_imp_not.mpr $ @Satisfies.formula_hereditary (M := M) (w := Sum.inl ()) (w' := Sum.inr $ Sum.inr w₂) ψ (by aesop);
      exact satisfies_right_on_counterexampleDPModel.not.mp hψ;

instance : Entailment.Disjunctive (Hilbert.Int) := ⟨disjunctive⟩

end DP

end Hilbert.Int.Kripke


end LO.Propositional
