module
import Foundation.InterpretabilityLogic.Hilbert.Basic.Basic
import Foundation.InterpretabilityLogic.Hilbert.Minimal.Basic

namespace LO.InterpretabilityLogic

open LO.Modal.Entailment LO.InterpretabilityLogic.Entailment

instance equiv_CL_ILMinus_J1_J2 : InterpretabilityLogic.CL ≊ InterpretabilityLogic.ILMinus_J1_J2 := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro h;
    induction h using Hilbert.Basic.rec! with
    | axm s h => rcases h with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec => apply nec!; assumption;
    | _ => simp;
  . intro h;
    induction h using Hilbert.Minimal.rec! with
    | axm s h => rcases (by simpa [Hilbert.Minimal.buildAxioms] using h) with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec => apply nec!; assumption;
    | R1 h => apply R1; assumption;
    | R2 h => apply R2; assumption;
    | _ => simp;

instance equiv_IL_ILMinus_J1_J2_J5 : InterpretabilityLogic.IL ≊ InterpretabilityLogic.ILMinus_J1_J2_J5 := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro h;
    induction h using Hilbert.Basic.rec! with
    | axm s h => rcases h with (rfl | rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec => apply nec!; assumption;
    | _ => simp;
  . intro h;
    induction h using Hilbert.Minimal.rec! with
    | axm s h => rcases (by simpa [Hilbert.Minimal.buildAxioms] using h) with (rfl | rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec => apply nec!; assumption;
    | R1 h => apply R1; assumption;
    | R2 h => apply R2; assumption;
    | _ => simp;

end LO.InterpretabilityLogic
