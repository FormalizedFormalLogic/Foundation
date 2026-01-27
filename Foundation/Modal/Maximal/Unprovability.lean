module

public import Foundation.Modal.Maximal.Basic

@[expose] public section

namespace LO.Modal

variable {φ : Formula ℕ}

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Formula
open Hilbert
open Formula

namespace Triv

lemma unprovable_AxiomL : Modal.Triv ⊬ (Axioms.L (.atom a)) := by
  apply Triv.iff_provable_Cl.not.mpr;
  apply Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Triv


namespace Ver

lemma unprovable_AxiomP : Modal.Ver ⊬ Axioms.P := by
  apply Ver.iff_provable_Cl.not.mpr;
  apply Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end Ver


namespace K4

lemma provable_trivTranslated_Cl : Modal.K4 ⊢ φ → Propositional.Cl ⊢ φᵀ.toPropFormula := by
  intro h;
  apply Triv.iff_provable_Cl.mp;
  apply WeakerThan.pbl h;

lemma unprovable_AxiomL : Modal.K4 ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_trivTranslated_Cl;
  apply Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

end K4

instance : Modal.K4 ⪱ Modal.GL := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact K4.unprovable_AxiomL;


namespace GL

lemma provable_verTranslated_Cl : Modal.GL ⊢ φ → Propositional.Cl ⊢ φⱽ.toPropFormula := by
  intro h;
  induction h using Hilbert.Normal.rec! with
    | axm _ a =>
      rcases a with (rfl | rfl | rfl) <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => dsimp [verTranslate, Formula.toPropFormula]; cl_prover;

@[simp, grind .]
lemma unprovable_AxiomT : (Modal.GL) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_verTranslated_Cl;
  apply Cl.not_provable_of_exists_valuation;
  use (λ _ => False);
  tauto;

instance : Entailment.Consistent (Modal.GL) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;

end GL


theorem not_S4_weakerThan_GL : ¬(Modal.S4) ⪯ (Modal.GL) := by
  apply Entailment.not_weakerThan_iff.mpr;
  use (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact GL.unprovable_AxiomT;


end LO.Modal
end
