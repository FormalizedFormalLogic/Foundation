import Logic.FirstOrder.Basic.Soundness
import Logic.FirstOrder.Hauptsatz
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.Summary.FirstOrder

open LO.FirstOrder

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {T : Theory L}

/- Cut elimination for Tait-calculus -/
noncomputable example {Δ : Sequent L} : ⊢ᶜ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz

#print axioms DerivationCR.hauptsatz

/- Compactness theorem -/
example (T : Theory L) :
    Semantics.Satisfiableₛ T ↔
    ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.Satisfiableₛ (T' : Theory L) :=
  FirstOrder.compactness

#print axioms FirstOrder.compactness

/- Soundness theorem -/
example {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness

#print axioms FirstOrder.completeness

/- Completeness theorem -/
noncomputable example {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness

#print axioms FirstOrder.completeness

open Arith FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]

/- Gödel's first incompleteness theorem -/
example : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

#print axioms FirstOrder.Arith.first_incompleteness

/- Undecidable sentence  -/
example : T ⊬ undecidable T ∧ T ⊬ ~undecidable T :=
  FirstOrder.Arith.undecidable T

#print axioms FirstOrder.Arith.undecidable

end LO.Summary.FirstOrder
