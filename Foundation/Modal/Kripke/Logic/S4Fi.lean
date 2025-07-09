import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Entailment.KT
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Logic.Basic
import Foundation.Vorspiel.List.Chain


namespace LO.Modal


namespace Axioms

variable (p₀ p₁ p₂ q : Formula α)

protected abbrev Fi.ant : Formula α := (
  q ⋏ □(q ➝ ◇(∼q ⋏ ◇q)) ⋏
  ◇p₀ ⋏ (□(p₀ ➝ ∼◇p₁ ⋏ ∼◇p₂)) ⋏
  ◇p₁ ⋏ (□(p₁ ➝ ∼◇p₂ ⋏ ∼◇p₀)) ⋏
  ◇p₂ ⋏ (□(p₂ ➝ ∼◇p₀ ⋏ ∼◇p₁))
)

protected abbrev Fi := Fi.ant p₀ p₁ p₂ q ➝ ◇(◇p₀ ⋏ ◇p₁ ⋏ ∼◇p₂)

end Axioms



open Formula (atom)
open Formula.Kripke
open Kripke

protected abbrev Hilbert.S4Fi : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Fi (.atom 0) (.atom 1) (.atom 2) (.atom 3)}⟩
protected abbrev S4Fi := Hilbert.S4Fi.logic
notation "𝐒𝟒𝐅𝐢" => Modal.S4Fi

section S4Fi.unprovable_AxiomFi_ant

def S4Fi.unprovable_AxiomFi_ant.countermodel : Kripke.Model where
  World := (Unit × Fin 2) ⊕ (ℕ × Fin 3)
  Rel := fun x y =>
    match x, y with
    | Sum.inl (_, _), _ => True
    | Sum.inr _, Sum.inl _ => False
    | Sum.inr (n, i), Sum.inr (m, j) =>
      if      n = m     then i = j
      else if n = m + 1 then i ≠ j
      else    n ≥ m + 2
  Val w a :=
    match w, a with
    | Sum.inl (_, i), 3 => i = 0
    | Sum.inr (0, 0), 0 => True
    | Sum.inr (0, 1), 1 => True
    | Sum.inr (0, 2), 2 => True
    | _, _ => False

instance : S4Fi.unprovable_AxiomFi_ant.countermodel.IsReflexive := ⟨by
  intro x;
  match x with | Sum.inl _ | Sum.inr _ => simp [S4Fi.unprovable_AxiomFi_ant.countermodel]
⟩

instance : S4Fi.unprovable_AxiomFi_ant.countermodel.IsTransitive := ⟨by
  intro x y z;
  match x, y, z with
  | Sum.inl _, _, _ | Sum.inr _, Sum.inl _, _ | Sum.inr _, Sum.inr _, Sum.inl _ => simp [S4Fi.unprovable_AxiomFi_ant.countermodel]
  | Sum.inr (n, i), Sum.inr (m, j), Sum.inr (k, l) =>
    dsimp [S4Fi.unprovable_AxiomFi_ant.countermodel];
    grind;
⟩

/-- if `i ≤ 2`, `x ⊧ i` iff `x = (0, i)` -/
lemma S4Fi.unprovable_AxiomFi_ant.countermodel.iff_at_level0_satisfies {x : countermodel.World} {i : Fin 3} : Satisfies countermodel x (atom i.1) ↔ x = Sum.inr (0, i) := by
  constructor
  . contrapose!;
    match i with | 0 | 1 | 2 => simp_all [Satisfies, S4Fi.unprovable_AxiomFi_ant.countermodel];
  . rintro rfl;
    match i with
    | 0 | 1 | 2 =>
      simp [countermodel, Satisfies];

/-- if `i ≤ 2`, `(0, i)` can see only `(0, i)` -/
lemma S4Fi.unprovable_AxiomFi_ant.countermodel.only_self_at_level0 {y : countermodel} {i : Fin 3} : Sum.inr (0, i) ≺ y ↔ y = Sum.inr (0, i) := by
  match y with
  | Sum.inl _ => simp [S4Fi.unprovable_AxiomFi_ant.countermodel, Frame.Rel'];
  | Sum.inr (m, j) => simp [Frame.Rel', S4Fi.unprovable_AxiomFi_ant.countermodel]; tauto;

set_option push_neg.use_distrib true in
lemma S4Fi.unprovable_AxiomFi_ant.valid_AxiomFi : unprovable_AxiomFi_ant.countermodel.toFrame ⊧ Axioms.Fi (atom 0) (atom 1) (atom 2) (atom 3) := by
  intro V x;
  apply Satisfies.imp_def.mpr;

  intro h;
  repeat rw [Satisfies.and_def] at h;

  have ⟨h₁, h₂, hy₀, h₃, hy₁, h₄, hy₂, h₅⟩ := h;
  clear h;

  replace ⟨y₀, Rxy₀, hy₀⟩ := Satisfies.dia_def.mp hy₀;
  replace ⟨y₁, Rxy₁, hy₁⟩ := Satisfies.dia_def.mp hy₁;
  replace ⟨y₂, Rxy₂, hy₂⟩ := Satisfies.dia_def.mp hy₂;

  obtain ⟨i, rfl⟩ : ∃ i, x = Sum.inl ((), i) := by
    match x with
    | Sum.inl ((), i) => use i;
    | Sum.inr (n, i)  =>
      exfalso;
      sorry;
  have ⟨Ry₀₁, Ry₀₂⟩ : ¬y₀ ≺ y₁ ∧ ¬y₀ ≺ y₂ := by
    by_contra! hC;
    rcases Satisfies.and_def.mp $ @h₃ y₀ (by simp [Frame.Rel', unprovable_AxiomFi_ant.countermodel]) hy₀ with ⟨hy₁, hy₂⟩;
    rcases hC with (Ry | Ry);
    . apply (Satisfies.not_dia_def.mp hy₁ _) Ry; simpa;
    . apply (Satisfies.not_dia_def.mp hy₂ _) Ry; simpa;
  have ⟨Ry₁₂, Ry₁₀⟩ : ¬y₁ ≺ y₂ ∧ ¬y₁ ≺ y₀ := by
    by_contra! hC;
    rcases Satisfies.and_def.mp $ @h₄ y₁ (by simp [Frame.Rel', unprovable_AxiomFi_ant.countermodel]) hy₁ with ⟨hy₂, hy₀⟩;
    rcases hC with (Ry | Ry);
    . apply (Satisfies.not_dia_def.mp hy₂ _) Ry; simpa;
    . apply (Satisfies.not_dia_def.mp hy₀ _) Ry; simpa;
  have ⟨Ry₂₀, Ry₂₁⟩ : ¬y₂ ≺ y₀ ∧ ¬y₂ ≺ y₁ := by
    by_contra! hC;
    rcases Satisfies.and_def.mp $ @h₅ y₂ (by simp [Frame.Rel', unprovable_AxiomFi_ant.countermodel]) hy₂ with ⟨hy₀, hy₁⟩;
    rcases hC with (Ry | Ry);
    . apply (Satisfies.not_dia_def.mp hy₀ _) Ry; simpa;
    . apply (Satisfies.not_dia_def.mp hy₁ _) Ry; simpa;

  match y₀, y₁, y₂ with
  | Sum.inl y₀, _, _
  | _, Sum.inl y₁, _
  | _, _, Sum.inl y₂ =>
    sorry;
    -- simp_all [Frame.Rel', countermodel];
  | Sum.inr (n₀, i₀), Sum.inr (n₁, i₁), Sum.inr (n₂, i₂) =>
    clear Ry₀₁ Ry₀₂ Ry₁₂ Ry₁₀ Ry₂₀ Ry₂₁ Rxy₀ Rxy₁ Rxy₂;
    apply Satisfies.dia_def.mpr;
    let z : unprovable_AxiomFi_ant.countermodel.toFrame.World := Sum.inr (
      (max n₀ n₁) + 1,
      match i₀, i₁ with
      | 0, 0 => 1
      | 0, 1 => 2
      | 0, 2 => 1
      | 1, 0 => 2
      | 1, 1 => 2
      | 1, 2 => 0
      | 2, 0 => 1
      | 2, 1 => 0
      | 2, 2 => 0
    );
    have Rz₀ : z ≺ (Sum.inr (n₀, i₀)) := by
      dsimp [z];
      rcases (show max n₀ n₁ = n₀ ∨ max n₀ n₁ = n₁ by omega) with (h | h);
      . simp [h, Frame.Rel', countermodel];
        split <;> trivial;
      . simp [h, Frame.Rel', countermodel];
        split;
        . omega;
        . split;
          . split <;> trivial;
          . omega;
    have Rz₁ : z ≺ (Sum.inr (n₁, i₁)) := by
      dsimp [z];
      rcases (show max n₀ n₁ = n₀ ∨ max n₀ n₁ = n₁ by omega) with (h | h);
      . simp [h, Frame.Rel', countermodel];
        split;
        . omega;
        . split;
          . split <;> trivial;
          . omega;
      . simp [h, Frame.Rel', countermodel];
        split <;> trivial;
    use z;
    constructor;
    . simp [Frame.Rel', countermodel]
    . apply Satisfies.and_def.mpr;
      constructor;
      . apply Satisfies.dia_def.mpr;
        use Sum.inr (n₀, i₀);
      . apply Satisfies.and_def.mpr;
        constructor;
        . apply Satisfies.dia_def.mpr;
          use Sum.inr (n₁, i₁);
        . apply Satisfies.not_def.mpr;
          by_contra! hC;
          obtain ⟨u, Ryu, hu⟩ := Satisfies.dia_def.mp hC;
          obtain ⟨hu₀, hu₁⟩ := Satisfies.and_def.mp $ @h₅ u (countermodel.trans (by sorry) Ryu) hu;
          match u with
          | Sum.inl u => simp [z, Frame.Rel', countermodel] at Ryu;
          | Sum.inr (m, j) =>
            simp [z, Frame.Rel', countermodel] at Ryu;
            split at Ryu;
            . rcases (show n₀ + 1 = m ∨ n₁ + 1 = m by omega) with (rfl | rfl);
              . apply Satisfies.not_dia_def.mp hu₀ (Sum.inr (n₀, i₀)) ?_ $ hy₀;
                convert Rz₀;
                . omega;
                . exact Ryu.symm;
              . apply Satisfies.not_dia_def.mp hu₁ (Sum.inr (n₁, i₁)) ?_ $ hy₁;
                convert Rz₁;
                . omega;
                . exact Ryu.symm;
            . split at Ryu;
              . sorry;
              . sorry;

lemma S4Fi.unprovable_AxiomFi_ant.countermodel.countermodel_S4Fi : unprovable_AxiomFi_ant.countermodel.toFrame ⊧* 𝐒𝟒𝐅𝐢 := by
  constructor;
  intro φ hφ;
  simp only [Entailment.theory, Set.mem_setOf_eq] at hφ;
  induction hφ using Hilbert.Normal.rec! with
  | mdp ihφψ ihφ => apply ValidOnFrame.mdp ihφψ ihφ;
  | nec ihφ => apply ValidOnFrame.nec ihφ;
  | imply₁ => apply ValidOnFrame.imply₁;
  | imply₂ => apply ValidOnFrame.imply₂;
  | ec => apply ValidOnFrame.elimContra;
  | axm s ih =>
    rcases ih with (rfl | rfl | rfl | rfl);
    . apply ValidOnFrame.axiomK;
    . apply @validate_AxiomT_of_reflexive countermodel.toFrame (s 0);
    . apply @validate_AxiomFour_of_transitive countermodel.toFrame (s 0);
    . apply Formula.Kripke.ValidOnFrame.subst;
      apply S4Fi.unprovable_AxiomFi_ant.valid_AxiomFi;

lemma S4Fi.unprovable_AxiomFi_ant : 𝐒𝟒𝐅𝐢 ⊬ ∼Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3) := by
  suffices ∃ M : Model, M ⊧* 𝐒𝟒𝐅𝐢 ∧ ∃ x : M, x ⊧ (Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3)) by
    by_contra! hC;
    obtain ⟨M, hM₁, ⟨x, hM₂⟩⟩ := this;
    apply Satisfies.not_def.mp $ @hM₁.realize (f := ∼(Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3))) _ _ _ _ _ ?_ x;
    . assumption;
    . simpa using hC;
  use S4Fi.unprovable_AxiomFi_ant.countermodel;
  constructor;
  . constructor;
    intro φ hφ;
    apply S4Fi.unprovable_AxiomFi_ant.countermodel.countermodel_S4Fi.realize;
    assumption;
  . use Sum.inl ((), 0);
    simp only [Fin.isValue, Semantics.And.realize_and];
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩;
    . tauto;
    . intro x Rωx;
      match x with
      | Sum.inl ((), 1) | Sum.inr (n, i) => simp [Satisfies, unprovable_AxiomFi_ant.countermodel];
      | Sum.inl ((), 0) =>
        intro _;
        apply Satisfies.dia_def.mpr;
        use Sum.inl ((), 1);
        constructor;
        . tauto;
        . apply Satisfies.and_def.mpr;
          constructor;
          . apply Satisfies.not_def.mpr;
            simp [Semantics.Realize, Satisfies, unprovable_AxiomFi_ant.countermodel];
          . apply Satisfies.dia_def.mpr;
            use Sum.inl ((), 0);
            constructor;
            . tauto;
            . simp [Semantics.Realize, Satisfies, unprovable_AxiomFi_ant.countermodel];
    . apply Satisfies.dia_def.mpr;
      use Sum.inr (0, 0);
      tauto;
    . intro x Rωx hx;
      replace hx := @unprovable_AxiomFi_ant.countermodel.iff_at_level0_satisfies x 0 |>.mp hx;
      subst hx;
      apply Satisfies.and_def.mpr;
      constructor <;>
      . apply Satisfies.not_dia_def.mpr;
        intro y R0y;
        have := @unprovable_AxiomFi_ant.countermodel.only_self_at_level0 y 0 |>.mp R0y;
        subst y;
        simp [Semantics.Realize, Satisfies, unprovable_AxiomFi_ant.countermodel];
    . apply Satisfies.dia_def.mpr;
      use Sum.inr (0, 1);
      tauto;
    . intro x Rωx hx;
      replace hx := @unprovable_AxiomFi_ant.countermodel.iff_at_level0_satisfies x 1 |>.mp hx;
      subst hx;
      apply Satisfies.and_def.mpr;
      constructor <;>
      . apply Satisfies.not_dia_def.mpr;
        intro y R0y;
        have := @unprovable_AxiomFi_ant.countermodel.only_self_at_level0 y 1 |>.mp R0y;
        subst y;
        simp [Semantics.Realize, Satisfies, unprovable_AxiomFi_ant.countermodel];
    . apply Satisfies.dia_def.mpr;
      use Sum.inr (0, 2);
      tauto;
    . intro x Rωx hx;
      replace hx := @unprovable_AxiomFi_ant.countermodel.iff_at_level0_satisfies x 2 |>.mp hx;
      subst hx;
      apply Satisfies.and_def.mpr;
      constructor <;>
      . apply Satisfies.not_dia_def.mpr;
        intro y R0y;
        have := @unprovable_AxiomFi_ant.countermodel.only_self_at_level0 y 2 |>.mp R0y;
        subst y;
        simp [Semantics.Realize, Satisfies, unprovable_AxiomFi_ant.countermodel];

end S4Fi.unprovable_AxiomFi_ant


section

lemma S4Fi.infinite_of_not_valid_neg_AxiomFi_ant {M : Kripke.Model} (hM : M ⊧* 𝐒𝟒𝐅𝐢) : ¬(M ⊧ ∼Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3)) → Infinite M := by
  sorry

end

lemma S4Fi.no_finite_model_property : ¬(∀ φ, 𝐒𝟒𝐅𝐢 ⊬ φ → ∃ M : Kripke.Model, Finite M ∧ M ⊧* 𝐒𝟒𝐅𝐢 ∧ ¬M ⊧ φ) := by
  push_neg;
  use ∼Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3);
  constructor;
  . exact S4Fi.unprovable_AxiomFi_ant;
  . rintro M hM₁ hM₂;
    by_contra hC;
    apply not_finite_iff_infinite.mpr $ infinite_of_not_valid_neg_AxiomFi_ant hM₂ hC;
    assumption;

end LO.Modal
