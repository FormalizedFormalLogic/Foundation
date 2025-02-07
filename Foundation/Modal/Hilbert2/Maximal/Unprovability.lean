import Foundation.Modal.Hilbert2.Maximal.Basic
import Foundation.IntProp.Kripke.Classical

namespace LO.Modal

open System

open IntProp

open Hilbert
open Hilbert.Deduction
open Formula

namespace Hilbert


namespace Triv

lemma unprovable_AxiomL : Hilbert.Triv ⊬ (Axioms.L (.atom a)) := by
  apply Hilbert.Triv.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

end Triv


namespace Ver

lemma unprovable_AxiomP : (Hilbert.Ver) ⊬ Axioms.P := by
  apply Hilbert.Ver.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => True);
  simp;

end Ver


namespace K4

lemma provable_Cl_trivTranslated : (Hilbert.K4) ⊢! φ → (Hilbert.Cl _) ⊢! φᵀᴾ := by
  intro h;
  apply Hilbert.Triv.classical_reducible.mp;
  exact System.weakerThan_iff.mp K4_weakerThan_Triv h;

lemma unprovable_AxiomL : Hilbert.K4 ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_Cl_trivTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

end K4


namespace GL

lemma provable_CL_verTranslated : (Hilbert.GL) ⊢! φ → (Hilbert.Cl _) ⊢! φⱽᴾ := by
  intro h;
  induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [VerTranslation, toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [VerTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [VerTranslation, toPropFormula];

lemma unprovable_AxiomT : (Hilbert.GL) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_CL_verTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.T, VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

instance : System.Consistent (Hilbert.GL) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;

end GL

theorem not_S4_weakerThan_GL : ¬(Hilbert.S4) ≤ₛ (Hilbert.GL) := by
  apply System.not_weakerThan_iff.mpr;
  existsi (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact GL.unprovable_AxiomT;

end Hilbert


end LO.Modal
