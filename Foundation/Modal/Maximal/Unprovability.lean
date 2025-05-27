import Foundation.Modal.Maximal.Basic
import Foundation.Propositional.ClassicalSemantics.Hilbert
import Foundation.Modal.Entailment.GL

namespace LO.Modal

open Entailment

open Propositional
open Formula
open Entailment
open Hilbert
open Hilbert.Deduction
open Formula

namespace Logic


namespace Triv

lemma unprovable_AxiomL : Hilbert.Triv ⊬ (Axioms.L (.atom a)) := by
  apply Hilbert.Triv.iff_provable_Cl.not.mpr;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Triv


namespace Ver

lemma unprovable_AxiomP : (Hilbert.Ver) ⊬ Axioms.P := by
  apply Hilbert.Ver.iff_provable_Cl.not.mpr;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Ver


namespace K4

lemma provable_trivTranslated_Cl : (Hilbert.K4) ⊢! φ → (Hilbert.Cl) ⊢! φᵀ.toPropFormula := by
  intro h;
  apply Hilbert.Triv.iff_provable_Cl.mp;
  exact Entailment.weakerThan_iff.mp K4_weakerThan_Triv h;

lemma unprovable_AxiomL : Hilbert.K4 ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_trivTranslated_Cl;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end K4

instance : ProperSublogic Logic.K4 Logic.GL := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.K4 ⊢! φ by tauto;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact K4.unprovable_AxiomL;
⟩



namespace GL

lemma provable_verTranslated_Cl : (Hilbert.GL) ⊢! φ → (Hilbert.Cl) ⊢! φⱽ.toPropFormula := by
  intro h;
  induction h using Hilbert.Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];

lemma unprovable_AxiomT : (Hilbert.GL) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_verTranslated_Cl;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

instance : Entailment.Consistent (Hilbert.GL) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;

end GL

theorem not_S4_weakerThan_GL : ¬(Hilbert.S4) ⪯ (Hilbert.GL) := by
  apply Entailment.not_weakerThan_iff.mpr;
  use (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact GL.unprovable_AxiomT;

end Logic


end LO.Modal
