import Logic.FirstOrder.Basic.Soundness
import Logic.FirstOrder.Hauptsatz
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.Summary.FirstOrder

open LO.FirstOrder

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {T : Theory L}

/- Cut elimination for Tait-calculus -/
theorem cut_elimination {Δ : Sequent L} : ⊢ᶜ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz

/- Compactness theorem -/
theorem compactness_theorem (T : Theory L) :
    Semantics.Satisfiableₛ T ↔ ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.Satisfiableₛ (T' : Theory L) :=
  FirstOrder.compactness

/- Soundness theorem -/
theorem soundness_theorem {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness

/- Completeness theorem -/
theorem completeness_theorem {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness

open Arith FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]

/- Gödel's first incompleteness theorem -/
theorem first_incompleteness_theorem : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

/- Undecidable sentence  -/
theorem undecidable_sentence : T ⊬ undecidableSentence T ∧ T ⊬ ~undecidableSentence T :=
  FirstOrder.Arith.undecidable T

end LO.Summary.FirstOrder
