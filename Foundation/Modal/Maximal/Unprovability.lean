import Foundation.Modal.Maximal.Basic
import Foundation.Propositional.ClassicalSemantics.Hilbert
import Foundation.Modal.Entailment.GL

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Formula
open Hilbert
open Hilbert.Deduction
open Formula

namespace Logic


namespace Triv

lemma unprovable_AxiomL : Logic.Triv ⊬ (Axioms.L (.atom a)) := by
  apply Logic.Triv.iff_provable_Cl.not.mpr;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Triv


namespace Ver

lemma unprovable_AxiomP : (Logic.Ver) ⊬ Axioms.P := by
  apply Logic.Ver.iff_provable_Cl.not.mpr;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Ver


namespace K4

lemma provable_trivTranslated_Cl : (Logic.K4) ⊢! φ → (Hilbert.Cl) ⊢! φᵀ.toPropFormula := by
  intro h;
  apply Logic.Triv.iff_provable_Cl.mp;
  apply WeakerThan.pbl h;

lemma unprovable_AxiomL : Logic.K4 ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_trivTranslated_Cl;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end K4

instance : Logic.K4 ⪱ Logic.GL := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact K4.unprovable_AxiomL;


namespace GL

lemma provable_verTranslated_Cl : (Logic.GL) ⊢! φ → (Hilbert.Cl) ⊢! φⱽ.toPropFormula := by
  intro h;
  induction h with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];

lemma unprovable_AxiomT : (Logic.GL) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_verTranslated_Cl;
  apply Hilbert.Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

instance : Entailment.Consistent (Logic.GL) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;

end GL

theorem not_S4_weakerThan_GL : ¬(Logic.S4) ⪯ (Logic.GL) := by
  apply Entailment.not_weakerThan_iff.mpr;
  use (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact GL.unprovable_AxiomT;

end Logic


end LO.Modal
