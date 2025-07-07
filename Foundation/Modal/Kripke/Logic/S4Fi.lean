import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Entailment.KT
import Foundation.Modal.Hilbert.WellKnown
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

protected abbrev Hilbert.S4Fi : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Fi (.atom 0) (.atom 1) (.atom 2) (.atom 3)}⟩
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
  match x with
  | Sum.inl _ => simp [S4Fi.unprovable_AxiomFi_ant.countermodel];
  | Sum.inr _ => simp [S4Fi.unprovable_AxiomFi_ant.countermodel];
⟩

instance : S4Fi.unprovable_AxiomFi_ant.countermodel.IsTransitive := ⟨by
  intro x y z;
  match x, y, z with
  | Sum.inl _, _, _ | Sum.inr _, Sum.inl _, _ | Sum.inr _, Sum.inr _, Sum.inl _ =>
    simp [S4Fi.unprovable_AxiomFi_ant.countermodel];
  | Sum.inr (n, i), Sum.inr (m, j), Sum.inr (k, l) =>
    dsimp [S4Fi.unprovable_AxiomFi_ant.countermodel];
    grind;
⟩

/-- if `i ≤ 2`, `x ⊧ i` iff `x = (0, i)` -/
lemma S4Fi.unprovable_AxiomFi_ant.countermodel.iff_at_level0_satisfies {x : countermodel} {i : Fin 3} : x ⊧ (atom i.1) ↔ x = Sum.inr (0, i) := by
  constructor
  . contrapose!;
    match i with | 0 | 1 | 2 => simp_all [Semantics.Realize, Satisfies, S4Fi.unprovable_AxiomFi_ant.countermodel];
  . rintro rfl;
    match i with | 0 | 1 | 2 => simp [Semantics.Realize, Satisfies, countermodel];

/-- if `i ≤ 2`, `(0, i)` can see only `(0, i)` -/
lemma S4Fi.unprovable_AxiomFi_ant.countermodel.only_self_at_level0 {y : countermodel} {i : Fin 3} : Sum.inr (0, i) ≺ y ↔ y = Sum.inr (0, i) := by
  match y with
  | Sum.inl _ => simp [Frame.Rel', countermodel];
  | Sum.inr (m, j) => simp [Frame.Rel', countermodel]; tauto;



lemma S4Fi.unprovable_AxiomFi_ant.countermodel.countermodel_S4Fi : unprovable_AxiomFi_ant.countermodel ⊧* 𝐒𝟒𝐅𝐢 := by
  constructor;
  intro φ hφ;
  replace hφ := Logic.iff_provable.mpr hφ;
  induction hφ with
  | mdp ihφψ ihφ => apply ValidOnModel.mdp ihφψ ihφ;
  | nec ihφ => apply ValidOnModel.nec ihφ;
  | imply₁ => apply ValidOnModel.imply₁;
  | imply₂ => apply ValidOnModel.imply₂;
  | ec => apply ValidOnModel.elimContra;
  | maxm ih =>
    rcases (by simpa using ih) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
    . apply ValidOnModel.axiomK;
    . apply @validate_AxiomT_of_reflexive countermodel.toFrame (s 0);
    . apply @validate_AxiomFour_of_transitive countermodel.toFrame (s 0);
    . intro x h;
      apply Satisfies.dia_def.mpr;
      use Sum.inr (1, 2);
      constructor;
      . match x with
        | Sum.inl _
        | Sum.inr (2, 0)
        | Sum.inr (2, 1)
        | Sum.inr (1, 2)
        | Sum.inr (n + 3, i) =>
          simp [Frame.Rel', countermodel];
        | Sum.inr (0, i)
        | Sum.inr (1, 0)
        | Sum.inr (1, 1)
        | Sum.inr (2, 2) =>
          have := Satisfies.and_def.mp h |>.1;
          sorry;
      . simp only [Semantics.And.realize_and];
        refine ⟨?_, ?_, ?_⟩;
        . apply Satisfies.dia_def.mpr;
          use Sum.inr (0, 0);
          constructor;
          . simp [Frame.Rel', countermodel];
          . sorry;
        . apply Satisfies.dia_def.mpr;
          use Sum.inr (0, 1);
          constructor;
          . simp [Frame.Rel', countermodel];
          . sorry;
        . apply Satisfies.not_def.mpr;
          apply Satisfies.not_dia_def.mpr;
          intro y R12y;
          have : y = Sum.inr (0, 0) ∨ y = Sum.inr (0, 1) ∨ y = Sum.inr (1, 2) := by sorry;
          rcases this with (rfl | rfl | rfl);
          . sorry;
          . sorry;
          . sorry;

lemma S4Fi.unprovable_AxiomFi_ant : 𝐒𝟒𝐅𝐢 ⊬ ∼Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3) := by
  suffices ∃ M : Model, M ⊧* 𝐒𝟒𝐅𝐢 ∧ ∃ x : M, x ⊧ (Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3)) by
    by_contra! hC;
    obtain ⟨M, hM₁, ⟨x, hM₂⟩⟩ := this;
    apply Satisfies.not_def.mp $ @hM₁.realize (f := ∼(Axioms.Fi.ant (.atom 0) (.atom 1) (.atom 2) (.atom 3))) _ _ _ _ _ ?_ x;
    . assumption;
    . simpa using hC;
  use S4Fi.unprovable_AxiomFi_ant.countermodel;
  constructor;
  . exact S4Fi.unprovable_AxiomFi_ant.countermodel.countermodel_S4Fi;
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
