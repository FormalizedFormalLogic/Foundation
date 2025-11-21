import Foundation.Propositional.Formula
import Foundation.Propositional.Entailment.Cl.Basic
import Foundation.Vorspiel.List.Supplemental
import Foundation.Vorspiel.Finset.Supplemental
import Foundation.Vorspiel.Set.Supplemental
import Foundation.Propositional.Hilbert.Corsi.Disjunctive
import Foundation.Propositional.Kripke2.Basic

namespace LO.Propositional

open LO.Entailment (disjunctive)
open LO.Propositional.Entailment.Corsi
open Formula

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

structure FTheory (L : Logic ℕ) where
  protected theory : FormulaSet ℕ
  protected no_bot : ⊥ ∉ theory
  protected andIR : ∀ {φ ψ}, φ ∈ theory → ψ ∈ theory → φ ⋏ ψ ∈ theory
  protected imp_closed : ∀ {φ ψ}, L ⊢ φ ➝ ψ → φ ∈ theory → ψ ∈ theory
  protected L_subset : L ⊆ theory

attribute [simp] FTheory.no_bot

namespace FTheory

-- abbrev CanonicalRel : Rel FTheory FTheory := λ T₁ T₂ => ∀ {φ ψ}, φ ➝ ψ ∈ T₁.theory → φ ∈ T₂.theory → ψ ∈ T₂.theory

end FTheory

variable {L : Logic ℕ} [Entailment.F L]

structure PrimeFTheory (L : Logic ℕ) extends FTheory L where
  protected prime : ∀ {φ ψ}, φ ⋎ ψ ∈ theory → φ ∈ theory ∨ ψ ∈ theory


namespace FTheory.lindenbaum

end FTheory.lindenbaum


lemma FTheory.lindenbaum {χ ξ : Formula _} (T : FTheory L) (hT : χ ➝ ξ ∉ T.theory) : ∃ U : PrimeFTheory L,
  (∀ φ ψ, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory) ∧
  χ ∈ U.theory ∧ ξ ∉ U.theory
   := by sorry

abbrev emptyPrimeFTheory (L : Logic _) [Entailment.F L] [Entailment.Disjunctive L] : PrimeFTheory L where
  theory := L
  no_bot := by
    sorry;
  andIR hφ hψ := by
    simp only [←Logic.iff_provable] at hφ hψ ⊢;
    apply andIR <;> assumption;
  imp_closed := by
    intros φ ψ hφψ hφ;
    simp only [←Logic.iff_provable] at hφψ hφ ⊢;
    exact hφψ ⨀ hφ;
  L_subset := by tauto;
  prime {φ ψ} hφψ := by
    simp only [←Logic.iff_provable] at hφψ ⊢;
    exact disjunctive hφψ;

instance [Entailment.F L] [Entailment.Disjunctive L] : Nonempty (PrimeFTheory L) := ⟨emptyPrimeFTheory L⟩


namespace Kripke2

variable [Entailment.Disjunctive L]
variable {φ ψ χ : Formula ℕ}

open Formula.Kripke2

abbrev cannonicalModel (L : Logic ℕ) [Entailment.F L] [Entailment.Disjunctive L] : Kripke2.Model where
  World := PrimeFTheory L
  Rel T U := ∀ {φ ψ}, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory
  Val T a := (atom a) ∈ T.theory
  root := emptyPrimeFTheory L
  rooted := by
    intro T φ ψ hφψ hφ;
    rw [←Logic.iff_provable] at hφψ;
    exact T.imp_closed hφψ hφ;

lemma truthlemma {T : cannonicalModel L} : Satisfies _ T φ ↔ φ ∈ T.theory := by
  induction φ generalizing T with
  | hatom a => simp [Kripke2.Satisfies];
  | hfalsum => simp [Kripke2.Satisfies];
  | hor φ ψ ihφ ihψ =>
    suffices φ ∈ T.theory ∨ ψ ∈ T.theory ↔ φ ⋎ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro (hφ | hψ);
      . apply T.imp_closed orIntroL hφ;
      . apply T.imp_closed orIntroR hψ;
    . apply T.prime;
  | hand φ ψ ihφ ihψ =>
    suffices (φ ∈ T.theory ∧ ψ ∈ T.theory) ↔ φ ⋏ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply T.andIR hφ hψ;
    . intro h;
      constructor;
      . apply T.imp_closed andElimL h;
      . apply T.imp_closed andElimR h;
  | himp φ ψ ihφ ihψ =>
    suffices (∀ {U : cannonicalModel L}, T ≺ U → φ ∈ U.theory → ψ ∈ U.theory) ↔ φ ➝ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . contrapose!;
      exact FTheory.lindenbaum T.toFTheory;
    . rintro hφψ U RTU hφ;
      apply RTU hφψ hφ;

theorem provable_of_validOnCannonicalModel : (cannonicalModel L) ⊧ φ → L ⊢ φ := by
  contrapose!;
  intro h;
  apply ValidOnModel.not_of_exists_world;
  use (emptyPrimeFTheory L);
  apply truthlemma.not.mpr;
  apply Logic.iff_unprovable.mp;
  simpa;

end Kripke2

end LO.Propositional
