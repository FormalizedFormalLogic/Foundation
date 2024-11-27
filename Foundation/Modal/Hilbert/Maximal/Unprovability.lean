import Foundation.Modal.Hilbert.Maximal.Basic
import Foundation.Modal.Hilbert.WeakerThan.K4_Triv
import Foundation.IntProp.Kripke.Classical

namespace LO.Modal

open System

open IntProp

open Hilbert
open Hilbert.Deduction
open Formula

variable {α} [DecidableEq α]

namespace Hilbert


namespace Triv

lemma unprovable_AxiomL : Hilbert.Triv ℕ ⊬ (Axioms.L (.atom a)) := by
  apply Hilbert.Triv.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

end Triv


namespace Ver

lemma unprovable_AxiomP : (Hilbert.Ver ℕ) ⊬ Axioms.P := by
  apply Hilbert.Ver.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => True);
  simp;

end Ver


namespace K4

lemma provable_Cl_trivTranslated : (Hilbert.K4 α) ⊢! φ → (Hilbert.Cl α) ⊢! φᵀᴾ := by
  intro h;
  apply Hilbert.Triv.classical_reducible.mp;
  exact System.weakerThan_iff.mp Hilbert.K4_weakerThan_Triv h;

lemma unprovable_AxiomL : Hilbert.K4 ℕ ⊬ (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_Cl_trivTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

end K4


namespace GL

lemma provable_CL_verTranslated : (Hilbert.GL α) ⊢! φ → (Hilbert.Cl α) ⊢! φⱽᴾ := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;>
      { simp only [VerTranslation]; trivial; };
    | hMdp ih₁ ih₂ =>
      dsimp [VerTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [VerTranslation]; exact imp_id!;
    | _ => dsimp [VerTranslation]; trivial;

lemma unprovable_AxiomT : (Hilbert.GL ℕ) ⊬ Axioms.T (.atom a) := by
  apply not_imp_not.mpr provable_CL_verTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  use (λ _ => False);
  simp [Axioms.T, VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];

instance : System.Consistent (Hilbert.GL ℕ) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;

end GL

theorem not_S4_weakerThan_GL : ¬(Hilbert.S4 ℕ) ≤ₛ (Hilbert.GL ℕ) := by
  apply System.not_weakerThan_iff.mpr;
  existsi (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact GL.unprovable_AxiomT;

end Hilbert


end LO.Modal
