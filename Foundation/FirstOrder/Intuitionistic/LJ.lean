module

public import Foundation.Vorspiel.Multiset
public import Foundation.Vorspiel.Option
public import Foundation.FirstOrder.Intuitionistic.Rew

/-! # First-order $\mathbf{LJ}$ -/

@[expose] public section

namespace LO.FirstOrder.LJ

variable {L : Language}

open Semiformulaᵢ

abbrev Sequent (L : Language) := Multiset (Propositionᵢ L)

abbrev Head (L : Language) := Option (Propositionᵢ L)

namespace Head

def shift (Ξ : Head L) : Head L := Ξ.map Rewriting.shift

@[simp] lemma shift_none : shift (none : Head L) = none := rfl

@[simp] lemma shift_some (φ : Propositionᵢ L) : shift φ = some (Rewriting.shift φ) := rfl

end Head

inductive Derivation : Sequent L → Head L → Type _
/-- Identity rule -/
| identity (R : L.Rel k) (v) : Derivation ⦃rel R v⦄ (rel R v)
/-- Cut rule -/
| cut {φ : Propositionᵢ L} {Γ Δ Ξ} :
  Derivation Γ φ → Derivation (Δ + ⦃φ⦄) Ξ → Derivation (Γ + Δ) Ξ
/-- Structural rule -/
| contraction {Γ Γ' : Multiset (Propositionᵢ L)} {Ξ Ξ' : Option (Propositionᵢ L)} :
  Derivation Γ Ξ → Γ ⊆ Γ' → Ξ ⊆ Ξ' → Derivation Γ' Ξ'
/-- Positive introduction of verum -/
| verum : Derivation 0 (some ⊤)
/-- Negative introduction of falsum -/
| falsum : Derivation ⦃⊥⦄ none
/-- Positive introduction of implication -/
| positiveImply {φ ψ : Propositionᵢ L} :
  Derivation (Γ + ⦃φ⦄) ψ → Derivation Γ (φ 🡒 ψ)
/-- Negative introduction of implication -/
| negativeImply {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation (Δ + ⦃ψ⦄) Ξ → Derivation (Γ + Δ + ⦃φ 🡒 ψ⦄) Ξ
/-- Positive introduction of conjunction -/
| positiveAnd {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation Γ ψ → Derivation Γ (φ ⋏ ψ)
/-- Negative introduction of conjunction -/
| negativeAnd {φ ψ : Propositionᵢ L} :
  Derivation (Γ + ⦃φ, ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋏ ψ⦄) Ξ
/-- Positive introduction of disjunction (left) -/
| positiveOrLeft {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation Γ (φ ⋎ ψ)
/-- Positive introduction of disjunction (right) -/
| positiveOrRight {φ ψ : Propositionᵢ L} :
  Derivation Γ ψ → Derivation Γ (φ ⋎ ψ)
/-- Negative introduction of disjunction -/
| negativeOr :
  Derivation (Γ + ⦃φ⦄) Ξ → Derivation (Γ + ⦃ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋎ ψ⦄) Ξ
/-- Positive introduction of universal quantifier -/
| positiveForall {φ : Semipropositionᵢ L 1} :
  Derivation Γ⁺ᵐ (Rewriting.free φ) → Derivation Γ (∀¹ φ)
/-- Negative introduction of universal quantifier -/
| negativeForall {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
  Derivation (Γ + ⦃φ/[t]⦄) Ξ → Derivation (Γ + ⦃∀¹ φ⦄) Ξ
/-- Positive introduction of existential quantifier -/
| positiveExists {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
  Derivation Γ (φ/[t]) → Derivation Γ (∃¹ φ)
/-- Negative introduction of existential quantifier -/
| negativeExists {φ : Semipropositionᵢ L 1} :
  Derivation (Γ⁺ᵐ + ⦃Rewriting.free φ⦄) Ξ.shift → Derivation (Γ + ⦃∃¹ φ⦄) Ξ

infix:45 " ⊢ᴸᴶ¹ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L} {Ξ Λ : Head L}

def cast (d : Γ ⊢ᴸᴶ¹ Ξ) (seq : Γ = Δ := by abel) (heq : Ξ = Λ := by simp) : Δ ⊢ᴸᴶ¹ Λ := seq ▸ heq ▸ d

def eta : (φ : Propositionᵢ L) → ⦃φ⦄ ⊢ᴸᴶ¹ φ
  | .rel R v => identity R v
  |        ⊥ => contraction falsum (by simp) (by simp)
  |    φ ⋏ ψ => positiveAnd
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
        contraction (eta φ) (by simpa using Multiset.subset_add_left) (by simp)))
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
        contraction (eta ψ) (by simpa using Multiset.subset_add_right) (by simp)))
  |    φ ⋎ ψ => negativeOr (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ ⋎ ψ)
      (cast (positiveOrLeft (ψ := ψ) (eta φ)))
      (cast (positiveOrRight (φ := φ) (eta ψ)))
  |    φ 🡒 ψ => positiveImply <|
      cast (negativeImply (φ := φ) (ψ := ψ) (Δ := 0) (Ξ := ψ)
        (eta φ)
        (cast (eta ψ) (by simp) (by simp)))
  |     ∀¹ φ => positiveForall (Γ := ⦃∀¹ φ⦄) <|
      cast (negativeForall (Γ := 0) (Ξ := Rewriting.free φ) (φ := Rewriting.shift φ) (t := &0) <|
        cast (eta (Rewriting.free φ)) (by simp) (by simp)) (by simp)
  |     ∃¹ φ => negativeExists (Γ := 0) (Ξ := ∃¹ φ) <|
      cast (positiveExists (Γ := ⦃Rewriting.free φ⦄) (φ := Rewriting.shift φ) (t := &0) <|
        cast (eta (Rewriting.free φ)) (by simp) (by simp))
  termination_by φ => φ.complexity

end Derivation

end LO.FirstOrder.LJ
