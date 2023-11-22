import Logic.FirstOrder.Basic.Soundness
import Logic.FirstOrder.Hauptsatz
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.Summary.FirstOrder

open LO.FirstOrder

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {T : Theory L}

theorem cut_elimination {Δ : Sequent L} : ⊢ᶜ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz

theorem soundness_theorem {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness

theorem completeness_theorem {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness

open Arith FirstIncompleteness

variable (T : Theory ℒₒᵣ) [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

theorem first_incompleteness_theorem : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

theorem undecidable_sentence :
    ¬T ⊢! undecidableSentence T ∧ ¬T ⊢! ~undecidableSentence T :=
  FirstOrder.Arith.undecidable T

end LO.Summary.FirstOrder
