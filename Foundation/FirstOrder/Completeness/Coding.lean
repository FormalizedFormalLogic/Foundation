import Foundation.FirstOrder.Basic

namespace LO

namespace FirstOrder

open Semiformula
variable {L : Language.{u}}

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.upper).foldr max 0

lemma not_fvar?_newVar {φ : SyntacticFormula L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ (newVar Γ) :=
  not_fvar?_of_lt_upper φ (by simpa[newVar] using List.le_max_of_le (List.mem_map_of_mem _ h) (by simp))

namespace Derivation

open Semiformula
variable {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L}

def allNvar {φ} (h : ∀' φ ∈ Δ) : T ⟹ φ/[&(newVar Δ)] :: Δ → T ⟹ Δ := fun b ↦
  let b : T ⟹ (∀' φ) :: Δ :=
    genelalizeByNewver (by simpa[FVar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Tait.wk b (by simp[h])

protected def id {φ} (hp : φ ∈ T) : T ⟹ ∼∀∀ φ :: Δ → T ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (toClose (root hp)) (by simp)) b

end Derivation

namespace System

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.Rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSemiformula L 1 → Code L
  | ex : SyntacticSemiformula L 1 → SyntacticTerm L → Code L
  | id : SyntacticFormula L → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.Rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSemiformula L 1) ⊕
    (SyntacticSemiformula L 1 × SyntacticTerm L) ⊕
    (SyntacticFormula L) where
  toFun := fun c =>
    match c with
    | (Code.axL r v) => Sum.inl ⟨_, r, v⟩
    | Code.verum     => Sum.inr $ Sum.inl ()
    | (Code.and φ ψ) => Sum.inr $ Sum.inr $ Sum.inl (φ, ψ)
    | (Code.or φ ψ)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, ψ)
    | (Code.all φ)   => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl φ
    | (Code.ex φ t)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, t)
    | (Code.id φ)    => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr φ
  invFun := fun x =>
    match x with
    | (Sum.inl ⟨_, r, v⟩)                                                => Code.axL r v
    | (Sum.inr $ Sum.inl ())                                             => Code.verum
    | (Sum.inr $ Sum.inr $ Sum.inl (φ, ψ))                               => Code.and φ ψ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, ψ))                     => Code.or φ ψ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl φ)                => Code.all φ
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (φ, t)) => Code.ex φ t
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr φ)      => Code.id φ
  left_inv := fun c => by cases c <;> simp
  right_inv := fun x => by
    rcases x with (⟨_, _, _⟩ | ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _) <;> simp

instance [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [∀ k, Encodable (L.Func k)] [∀ k, Encodable (L.Rel k)] :
    Encodable (Code L) :=
  haveI : Encodable Empty := IsEmpty.toEncodable
  Encodable.ofEquiv _ (Code.equiv L)

end System

end FirstOrder

end LO
