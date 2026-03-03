module

public import Foundation.Propositional.Kripke3.Logic.Int.Completeness

@[expose] public section

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Int

variable {κ₁ κ₂ : Type*} [Nonempty κ₁] [Nonempty κ₂]
         {M₁ : KripkeModel κ₁ ℕ} {M₂ : KripkeModel κ₂ ℕ} [M₁.Intuitionistic] [M₂.Intuitionistic]
         {w₁ : M₁.world} {w₂ : M₂.world}
         {φ ψ : Formula ℕ}

abbrev countermodelDP
  (M₁ : KripkeModel κ₁ α) [M₁.Intuitionistic]
  (M₂ : KripkeModel κ₂ α) [M₂.Intuitionistic]
  (w₁ : M₁.world) (w₂ : M₂.world)
  : KripkeModel (Unit ⊕ κ₁ ⊕ κ₂) α where
  frame x y :=
    match x, y with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl y) => M₁.rel w₁ y
    | (Sum.inl _), (Sum.inr $ Sum.inr y) => M₂.rel w₂ y
    | (Sum.inr $ Sum.inl x), (Sum.inr $ Sum.inl y) => M₁.rel x y
    | (Sum.inr $ Sum.inr x), (Sum.inr $ Sum.inr y) => M₂.rel x y
    | _, _ => False
  val a w :=
    match w with
    | Sum.inr $ Sum.inl w => M₁ a w
    | Sum.inr $ Sum.inr w => M₂ a w
    | _ => False

instance : (countermodelDP M₁ M₂ w₁ w₂).Intuitionistic where
  refl x := by
    match x with
    | (Sum.inl _) => trivial
    | (Sum.inr $ Sum.inl x) => exact Std.Refl.refl x
    | (Sum.inr $ Sum.inr x) => exact Std.Refl.refl x
  trans := by
    simp only [
      countermodelDP, KripkeModel.rel, Sum.forall, forall_const, imp_self,
      implies_true, true_and, IsEmpty.forall_iff, and_true, and_self, imp_false
    ];
    refine ⟨?_, ?_, ?_⟩;
    . constructor;
      . apply Trans.trans;
      . apply Trans.trans;
    . apply Trans.trans;
    . apply Trans.trans;
  atom_persistency := by
    simp only [
      countermodelDP, KripkeModel.rel, KripkeModel.forces_atom, Sum.forall,
      imp_false, not_true_eq_false, implies_true, IsEmpty.forall_iff, and_self,
      not_false_eq_true, true_and, and_true,
    ];
    constructor <;> apply KripkeModel.Persistent.atom_persistency;

lemma counterexampleDPModel.forces_left {x : M₁.world} :
  x ⊩ φ ↔ ((countermodelDP M₁ M₂ w₁ w₂).Forces (Sum.inr $ Sum.inl x) φ) := by
  induction φ generalizing x with
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ y;
      match y with
      | (Sum.inl _) | (Sum.inr $ Sum.inr y) => simp [countermodelDP]
      | (Sum.inr $ Sum.inl y) => grind [hφψ y];
    . intro h y Rxy hφ;
      exact ihψ.mpr $ h (Sum.inr $ Sum.inl y) Rxy $ ihφ.mp $ hφ;
  | hatom => simp [KripkeModel.Forces, KripkeModel.forces_atom]
  | _ => simp_all [KripkeModel.Forces];

lemma counterexampleDPModel.forces_right {x : M₂.world} :
  x ⊩ φ ↔ ((countermodelDP M₁ M₂ w₁ w₂).Forces (Sum.inr $ Sum.inr x) φ) := by
  induction φ generalizing x with
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ y;
      match y with
      | (Sum.inl _) | (Sum.inr $ Sum.inl y) => simp [countermodelDP]
      | (Sum.inr $ Sum.inr y) => grind [hφψ y];
    . intro h y Rxy hφ;
      exact ihψ.mpr $ h (Sum.inr $ Sum.inr y) Rxy $ ihφ.mp $ hφ;
  | hatom => simp [KripkeModel.Forces, KripkeModel.forces_atom]
  | _ => simp_all [KripkeModel.Forces];

variable [Entailment.Consistent (Propositional.Int)]

theorem disjunctive : Propositional.Int ⊢ φ ⋎ ψ → Propositional.Int ⊢ φ ∨ Propositional.Int ⊢ ψ := by
  contrapose!;
  rintro ⟨hnφ, hnψ⟩;
  obtain ⟨_, _, M₁, _, w₁, h₁⟩ := exists_model_of_unprovable hnφ;
  obtain ⟨_, _, M₂, _, w₂, h₂⟩ := exists_model_of_unprovable hnψ;

  suffices ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ M : KripkeModel κ ℕ, ∃ w : M.world, w ⊮ φ ⋎ ψ by sorry;
  let M := countermodelDP M₁ M₂ w₁ w₂;
  have : M.Intuitionistic := by infer_instance;
  have : IsTrans _ M.rel := by sorry;

  refine ⟨_, _, M, Sum.inl (), ?_⟩
  apply M.forces_or.not.mpr;
  push_neg;
  constructor;
  . contrapose! h₁;
    exact counterexampleDPModel.forces_left.mpr $ by
      show M.Forces (Sum.inr $ Sum.inl w₁) φ;
      apply M.formula_persistency h₁;
      apply Std.Refl.refl;
  . contrapose! h₂;
    exact counterexampleDPModel.forces_right.mpr $ by
      show M.Forces (Sum.inr $ Sum.inr w₂) ψ;
      apply M.formula_persistency h₂;
      apply Std.Refl.refl;

instance : Entailment.Disjunctive Propositional.Int := ⟨disjunctive⟩

end Int


end LO.Propositional

end
