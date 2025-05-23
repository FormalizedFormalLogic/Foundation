import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Entailment.KT
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.AxiomMk
import Foundation.Modal.Logic.Basic
import Foundation.Vorspiel.List.Chain


namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Hilbert

protected abbrev S4Fine.fine_axiom_ant : Formula ℕ := (
  (.atom 0) ⋏ □((.atom 0) ➝ ◇(∼(.atom 0) ➝ ◇(.atom 0))) ⋏
  ◇(.atom 1) ⋏ □((.atom 1) ➝ ∼◇(.atom 2) ⋏ ∼◇(.atom 3)) ⋏
  ◇(.atom 2) ⋏ □((.atom 2) ➝ ∼◇(.atom 3) ⋏ ∼◇(.atom 1)) ⋏
  ◇(.atom 3) ⋏ □((.atom 3) ➝ ∼◇(.atom 1) ⋏ ∼◇(.atom 2))
)
protected abbrev S4Fine.fine_axiom := (S4Fine.fine_axiom_ant) ➝ ◇(◇(.atom 1) ⋏ ◇(.atom 2) ⋏ ∼◇(.atom 3))

protected abbrev S4Fine : Hilbert ℕ := ⟨{
  Axioms.K (.atom 0) (.atom 1),
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0),
  S4Fine.fine_axiom
}⟩
instance : (Hilbert.S4Fine).HasK where p := 0; q := 1;
instance : (Hilbert.S4Fine).HasT where p := 0
instance : (Hilbert.S4Fine).HasFour where p := 0
instance : Entailment.Modal.S4 (Hilbert.S4Fine) where

lemma S4_weakerThan_S4Fine : Hilbert.S4 ⪯ Hilbert.S4Fine := weakerThan_of_dominate_axioms $ by simp;


namespace S4Fine.Kripke

open Formula.Kripke
open Entailment

lemma unprovable_fine_axiom_ant : Hilbert.S4Fine ⊬ ∼S4Fine.fine_axiom_ant := by
  suffices ∃ M : Model, M.toFrame ⊧* Hilbert.S4Fine.logic ∧ ∃ x : M, x ⊧ S4Fine.fine_axiom_ant by
    by_contra! hC;
    obtain ⟨M, hM₁, ⟨x, hM₂⟩⟩ := this;
    apply Satisfies.not_def.mp $ hM₁.realize (f := ∼S4Fine.fine_axiom_ant) _ (by simpa) M.Val x;
    assumption;
  sorry;

mutual

def A (p q r : Formula ℕ) : ℕ → Formula ℕ
| 0 => p
| n + 1 => ◇(A p q r n) ⋏ ◇(B p q r n) ⋏ ∼◇(C p q r n)

def B (p q r : Formula ℕ) : ℕ → Formula ℕ
| 0 => q
| n + 1 => ◇(A p q r n) ⋏ ∼◇(B p q r n) ⋏ ◇(C p q r n)

def C (p q r : Formula ℕ) : ℕ → Formula ℕ
| 0 => r
| n + 1 => ∼◇(A p q r n) ⋏ ◇(B p q r n) ⋏ ◇(C p q r n)

end

open Formula in
lemma model_infinitity_of_fine_axiom_ant {M : Kripke.Model} (hM : M ⊧* Hilbert.S4Fine.logic)
  : (∃ x : M, x ⊧ S4Fine.fine_axiom_ant) → Infinite M := by
  rintro ⟨x, hx⟩;
  obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp $ (Satisfies.imp_def.mp $ hM.realize (f := S4Fine.fine_axiom) _ (by sorry) x) hx;

  dsimp [S4Fine.fine_axiom_ant] at hx;
  generalize (Formula.atom 0) = s at hx hy;
  generalize (Formula.atom 1) = p at hx hy;
  generalize (Formula.atom 2) = q at hx hy;
  generalize (Formula.atom 3) = r at hx hy;

  obtain ⟨hs₁, hs₂, hp₁, hp₂, hq₁, hq₂, hr₁, hr₂⟩ :
    x ⊧ s ∧ x ⊧ □(s ➝ ◇(∼s ➝ ◇s)) ∧
    x ⊧ ◇p ∧ x ⊧ □(p ➝ ∼◇q ⋏ ∼◇r) ∧
    x ⊧ ◇q ∧ x ⊧ □(q ➝ ∼◇r ⋏ ∼◇p) ∧
    x ⊧ ◇r ∧ x ⊧ □(r ➝ ∼◇p ⋏ ∼◇q) := by simpa using hx;
  obtain ⟨hp₃, hq₃, hr₃⟩ : y ⊧ ◇p ∧ y ⊧ ◇q ∧ y ⊧ ∼◇r := by simpa using hy;

  have H₁ : ∀ n : ℕ+, x ⊧ ◇(A p q r n) ∧ x ⊧ ◇(B p q r n) ∧ x ⊧ ◇(C p q r n) := by
    intro n;
    induction n with
    | one =>
      dsimp [A, B, C];
      refine ⟨?_, ?_, ?_⟩;
      . apply Satisfies.dia_def.mpr;
        use y;
      . apply Satisfies.dia_def.mpr;
        use y;
        suffices x ≺ y ∧ y ⊧ ◇p ∧ ¬y ⊧ ◇q ∧ y ⊧ ◇r by simpa;
        refine ⟨Rxy, ?_, ?_, ?_⟩;
        . assumption;
        . apply Satisfies.dia_def.not.mpr;
          push_neg;
          intro z Ryz hz;
          have := @hq₂ z (by sorry) hz;
          sorry;
        . sorry;
      . apply Satisfies.dia_def.mpr;
        use y;
        suffices x ≺ y ∧ ¬y ⊧ ◇p ∧ y ⊧ ◇q ∧ y ⊧ ◇r by  simpa;
        refine ⟨Rxy, ?_, ?_, ?_⟩;
        . sorry;
        . assumption;
        . sorry;
    | succ => sorry;
  replace H₁ : ∀ n : ℕ+, x ⊧ ◇(A p q r n) := λ n => H₁ n |>.1

  have H₂ : ∀ i j : ℕ+, Hilbert.S4 ⊢! (A p q r (i + j)) ➝ ∼(A p q r i) := by sorry;
  /-
  replace H₂ : ∀ i j : ℕ+, x ⊧ (A p q r (i + j)) ➝ ∼(A p q r i) := by
    intro i j;
    refine hM.realize (f := (A p q r (i + j)) ➝ ∼(A p q r i)) _ ?_ x;
    apply S4_weakerThan_S4Fine.subset;
    apply H₂;
  -/

  apply Infinite.of_injective (β := ℕ+)
  case f =>
    intro n;
    exact (Satisfies.dia_def.mp $ H₁ n) |>.choose;
  case hf =>
    intro i j;
    simp only;
    contrapose!;
    intro hij;
    generalize Satisfies.dia_def.mp (H₁ i) = hi;
    generalize Satisfies.dia_def.mp (H₁ j) = hj;
    sorry;

lemma no_finite_model_property : ¬(∀ φ, Hilbert.S4Fine ⊬ φ → ∃ M : Kripke.Model, Finite M ∧ M ⊧* Hilbert.S4Fine.logic ∧ ¬M ⊧ φ)  := by
  push_neg;
  use ∼S4Fine.fine_axiom_ant;
  constructor;
  . exact unprovable_fine_axiom_ant;
  . rintro M;
    contrapose!;
    rintro ⟨hM₁, hM₂⟩;
    apply not_finite_iff_infinite.mpr;
    apply model_infinitity_of_fine_axiom_ant hM₁;
    obtain ⟨x, hx⟩ := ValidOnModel.exists_world_of_not hM₂;
    use x;
    simpa using Satisfies.not_def.not.mp hx;

end S4Fine.Kripke


end Hilbert

end LO.Modal
