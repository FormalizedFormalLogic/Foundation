import Logic.Logic.HilbertStyle
import Logic.Modal.Normal.LogicSymbol
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [LO.Modal.Normal.ModalLogicSymbol F] [System F S]
variable (𝓢 : S)

class Necessitation where
  nec {p q : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

end LO.System

namespace LO.Modal.Normal

variable {α : Type*} [DecidableEq α]

inductive Deduction (Λ : AxiomSet α) : (Formula α) → Type _
  | maxm {p}       : p ∈ Λ → Deduction Λ p
  | mdp {p q}      : Deduction Λ (p ⟶ q) → Deduction Λ p → Deduction Λ q
  | nec {p}        : Deduction Λ p → Deduction Λ (□p)
  | verum          : Deduction Λ ⊤
  | imply₁ (p q)   : Deduction Λ (p ⟶ q ⟶ p)
  | imply₂ (p q r) : Deduction Λ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ (p q)    : Deduction Λ (p ⋏ q ⟶ p)
  | conj₂ (p q)    : Deduction Λ (p ⋏ q ⟶ q)
  | conj₃ (p q)    : Deduction Λ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ (p q)    : Deduction Λ (p ⟶ p ⋎ q)
  | disj₂ (p q)    : Deduction Λ (q ⟶ p ⋎ q)
  | disj₃ (p q r)  : Deduction Λ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne (p)        : Deduction Λ (~~p ⟶ p)

instance : LO.System (Formula α) (AxiomSet α) := ⟨Deduction⟩

open Deduction in
instance : LO.System.Classical (Λ : AxiomSet α) where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃
  dne := dne

open Deduction in
instance : LO.System.Necessitation (Λ : AxiomSet α) where
  nec := nec

end LO.Modal.Normal
