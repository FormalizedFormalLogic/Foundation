import Foundation.Modal.Hilbert.Maximal.Basic
import Foundation.Propositional.Kripke.Hilbert.Cl.Classical

namespace LO.Modal

open Entailment

open Propositional

open Hilbert
open Hilbert.Deduction
open Formula

namespace Hilbert


namespace Triv

lemma unprovable_AxiomL : Hilbert.Triv ⊬ (Axioms.L (.atom a)) := by
  apply Hilbert.Triv.iff_provable_Cl.not.mpr;
  apply Propositional.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.L, trivTranslate, toPropFormula, Propositional.Formula.Kripke.Satisfies];

end Triv


namespace Ver

lemma unprovable_AxiomP : (Hilbert.Ver) ⊬ Axioms.P := by
  apply Hilbert.Ver.iff_provable_Cl.not.mpr;
  apply Propositional.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [verTranslate, toPropFormula, Propositional.Formula.Kripke.Satisfies];
  use (λ _ => True);
  simp;

end Ver


namespace K4

lemma provable_trivTranslated_Cl : (Hilbert.K4) ⊢! φ → (Hilbert.Cl) ⊢! φᵀ.toPropFormula := by
  intro h;
  apply Hilbert.Triv.iff_provable_Cl.mp;
  exact Entailment.weakerThan_iff.mp K4_weakerThan_Triv h;

lemma unprovable_AxiomL : Hilbert.K4 ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_trivTranslated_Cl;
  apply Propositional.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [trivTranslate, toPropFormula, Propositional.Formula.Kripke.Satisfies];
  use (λ _ => False);
  simp;

end K4


namespace GL

lemma provable_verTranslated_Cl : (Hilbert.GL) ⊢! φ → (Hilbert.Cl) ⊢! φⱽ.toPropFormula := by
  intro h;
  induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];

lemma unprovable_AxiomT : (Hilbert.GL) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_verTranslated_Cl;
  apply Propositional.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [verTranslate, toPropFormula, Propositional.Formula.Kripke.Satisfies];
  use (λ _ => False);
  simp;

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

end Hilbert


end LO.Modal
