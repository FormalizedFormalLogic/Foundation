import Logic.FirstOrder.Basic.Soundness
import Logic.FirstOrder.Hauptsatz
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.Summary.FirstOrder

open LO.FirstOrder

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {T : Theory L}

/- Cut elimination for Tait-calculus -/
noncomputable example {Δ : Sequent L} : ⊢ᶜ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz

/- Compactness theorem -/
example (T : Theory L) :
    Semantics.Satisfiableₛ T ↔ ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.Satisfiableₛ (T' : Theory L) :=
  FirstOrder.compactness

/- Soundness theorem -/
example {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness

/- Completeness theorem -/
noncomputable example {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness

open Arith FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]

/- Gödel's first incompleteness theorem -/
example : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

/- Undecidable sentence  -/
example : T ⊬ undecidableSentence T ∧ T ⊬ ~undecidableSentence T :=
  FirstOrder.Arith.undecidable T

end LO.Summary.FirstOrder
