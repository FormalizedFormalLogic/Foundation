module
import Foundation.FirstOrder.Basic

namespace LO

namespace FirstOrder

open Semiformula
variable {L : Language.{u}}

namespace Entailment

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.Rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSemiformula L 1 → Code L
  | ex : SyntacticSemiformula L 1 → SyntacticTerm L → Code L
  | id : Sentence L → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.Rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSemiformula L 1) ⊕
    (SyntacticSemiformula L 1 × SyntacticTerm L) ⊕
    (Sentence L) where
  toFun := fun c =>
    match c with
    | (Code.axL r v) => Sum.inl ⟨_, r, v⟩
    | Code.verum     => Sum.inr $ Sum.inl ()
    | (Code.and φ ψ) => Sum.inr $ Sum.inr $ Sum.inl (φ, ψ)
    | (Code.or φ ψ)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, ψ)
    | (Code.all φ)   => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl φ
    | (Code.ex φ t)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, t)
    | (Code.id σ)    => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr σ
  invFun := fun x =>
    match x with
    | (Sum.inl ⟨_, r, v⟩)                                                => Code.axL r v
    | (Sum.inr $ Sum.inl ())                                             => Code.verum
    | (Sum.inr $ Sum.inr $ Sum.inl (φ, ψ))                               => Code.and φ ψ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, ψ))                     => Code.or φ ψ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl φ)                => Code.all φ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, t)) => Code.ex φ t
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr σ)      => Code.id σ
  left_inv := fun c => by cases c <;> simp
  right_inv := fun x => by
    rcases x with (⟨_, _, _⟩ | ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _) <;> simp

instance [L.DecidableEq] [L.Encodable] : Encodable (Code L) :=
  haveI : Encodable Empty := IsEmpty.toEncodable
  Encodable.ofEquiv _ (Code.equiv L)

end Entailment

end FirstOrder

end LO
