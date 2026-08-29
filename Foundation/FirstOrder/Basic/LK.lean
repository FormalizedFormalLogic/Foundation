module

/- public import Foundation.Logic.Calculus -/
public import Foundation.Logic.Calculus
public import Foundation.Propositional.Entailment.Int
public import Foundation.FirstOrder.Basic.Syntax.Rew
public import Mathlib.Data.List.MinMax

/-! # First-order $\mathbf{LK}$ -/

@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := Multiset (Proposition L)

namespace Sequent

open Semiformula

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : Proposition L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ Γ.newVar :=
  not_fvar?_of_lt_fvSup φ (by simp only [newVar]; sorry)

@[simp] lemma lcHom_comm {Γ : List (Formula L ξ)} (f : Formula L ξ →ˡᶜ Proposition L) :
    (∼Γ).map f = ∼Γ.map f := by simp [List.tilde_def]

def IsClosed (Γ : Sequent L) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

def embed (Γ : Multiset (Sentence L)) : Sequent L := Γ.map Rewriting.emb

@[simp] lemma embed_nil : embed (∅ : Multiset (Sentence L)) = ∅ := rfl

@[simp] lemma embed_add {Γ Δ : Multiset (Sentence L)} :
    embed (Γ + Δ) = embed Γ + embed Δ := by simp [embed]

@[simp] lemma embed_singleton {φ : Sentence L} :
    embed (⦃φ⦄ : Multiset (Sentence L)) = {↑φ} := rfl

@[simp] lemma embed_shift (Γ : Multiset (Sentence L)) :
    (embed Γ)⁺ᵐ = embed Γ := by
  simp [embed, Rewriting.shiftsM]

end Sequent

/-! ## Derivation for $\mathbf{LK}$ -/

/-- Derivation for $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| identity (r : L.Rel k) (v) : Derivation ⦃.rel r v, .nrel r v⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) → Derivation (Γ + ⦃φ ⋏ ψ⦄)
| all : Derivation (Γ⁺ᵐ + ⦃φ.free⦄) → Derivation (Γ + ⦃∀¹ φ⦄)
| exs : Derivation (Γ + ⦃φ/[t]⦄) → Derivation (Γ + ⦃∃¹ φ⦄)

prefix:45 "⊢ᴸᴷ¹ " => Derivation
