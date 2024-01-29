
import Logic.Propositional.Basic
import Logic.FirstOrder.Hauptsatz
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Incompleteness.FirstIncompleteness
import Logic.Modal.Normal.Completeness

namespace LO.Summary

namespace Propositional
open LO.Propositional

variable {α : Type*} {T : LO.Propositional.Theory α}

/-- Soundness theorem -/
noncomputable example {p : LO.Propositional.Formula α} :
  T ⊢ p → T ⊨ p := soundness

#print axioms soundness

/-- Completeness theorem -/
noncomputable example {p : LO.Propositional.Formula α} :
  T ⊨ p → T ⊢ p := completeness

#print axioms completeness

end Propositional

namespace FirstOrder

open LO.FirstOrder

variable {L : Language} {T : Theory L}

/-- Cut elimination for Tait-calculus -/
example [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  {Δ : Sequent L} : ⊢¹ Δ → { d : ⊢¹ Δ // Derivation.CutFree d } := Derivation.hauptsatz

#print axioms Derivation.hauptsatz

/-- Compactness theorem -/
example (T : Theory L) :
    Semantics.SatisfiableTheory T ↔
    ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.SatisfiableTheory (T' : Theory L) :=
  FirstOrder.compactness

#print axioms FirstOrder.compactness

/-- Soundness theorem -/
example {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness

#print axioms FirstOrder.completeness

/-- Completeness theorem -/
noncomputable example {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness

#print axioms FirstOrder.completeness

open Arith FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T]
  [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] [SigmaOneSound T] [Theory.Computable T]

/-- Gödel's first incompleteness theorem -/
example : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

#print axioms FirstOrder.Arith.first_incompleteness

/-- Undecidable sentence  -/
example : T ⊬ undecidable T ∧ T ⊬ ~undecidable T :=
  FirstOrder.Arith.undecidable T

#print axioms FirstOrder.Arith.undecidable

end FirstOrder

namespace Modal

open LO.Modal LO.Modal.Normal

variable {β : Type*} [DecidableEq β]

/-- Strong completeness theorem for 𝐊 -/
example : Completeness (𝐊 : AxiomSet β) (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β))) := LogicK.Hilbert.completes

#print axioms LogicK.Hilbert.completes

end Modal


end LO.Summary
