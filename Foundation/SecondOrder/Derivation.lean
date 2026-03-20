module

public import Foundation.SecondOrder.Syntax.Rew

@[expose] public section

/-!
# Second-order one-sided $\mathbf{LK}$
-/

namespace LO.SecondOrder

open FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := List (Proposition L)

namespace Sequent

def shift₀ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₀

@[simp] lemma shift₀_nil : shift₀ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₀_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₀ (φ :: Γ) = Semiproposition.shift₀ φ :: shift₀ Γ := rfl

def shift₁ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₁

@[simp] lemma shift₁_nil : shift₁ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₁_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₁ (φ :: Γ) = Semiproposition.shift₁ φ :: shift₁ Γ := rfl

instance : Tilde (Sequent L) := ⟨List.map (∼·)⟩

@[simp] lemma tilde_nil : ∼([] : Sequent L) = [] := rfl

@[simp] lemma tilde_cons (φ : Proposition L) (Γ : Sequent L) :
    ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

end Sequent

/-- Second-order one-sided $\mathbf{LK}$-derivation -/
inductive Derivation : Sequent L → Type _
| identity : Derivation [φ, ∼φ]
| cut : Derivation (φ :: Γ) → Derivation (∼φ :: Γ) → Derivation Γ
| wk : Derivation Γ → Γ ⊆ Δ → Derivation Δ
| verum : Derivation [⊤]
| and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
| or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
| all₀ {φ : Semiproposition L 0 1} : Derivation (φ.free₀ :: Sequent.shift₀ Γ) → Derivation ((∀⁰ φ) :: Γ)
| exs₀ {φ : Semiproposition L 0 1} : Derivation (φ/[t] :: Γ) → Derivation ((∃⁰ φ) :: Γ)
| all₁ {φ : Semiproposition L 1 0} : Derivation (φ.free₁ :: Sequent.shift₁ Γ) → Derivation ((∀¹ φ) :: Γ)
| exs₁ {φ : Semiproposition L 1 0} : Derivation (φ/⟦ψ⟧ :: Γ) → Derivation ((∃¹ φ) :: Γ)

scoped prefix:45 "⊢ᴷ " => Derivation

namespace Derivation

def cast {Γ Δ : Sequent L} (d : ⊢ᴷ Γ) (h : Γ = Δ) : ⊢ᴷ Δ := h ▸ d

end Derivation

abbrev Proof (φ : Sentence L) := ⊢ᴷ [(φ : Proposition L)]

inductive Proof.Symbol (L : Language) : Type
| symbol

notation "𝐋𝐊²" => Proof.Symbol.symbol

instance : Entailment (Proof.Symbol L) (Sentence L) := ⟨fun _ ↦ Proof⟩

/-! ## Proof system with axioms -/

abbrev Schema (L : Language) := Set (Proposition L)

protected structure Schema.Derivation (𝓢 : Schema L) (φ : Proposition L) where
  axioms : Sequent L
  derivation : Derivation (φ :: ∼axioms)
  isInstance : ∀ φ ∈ axioms, φ ∈ 𝓢

instance : Entailment (Schema L) (Proposition L) := ⟨Schema.Derivation⟩

/-! ## Theory: a set of provable sentences -/

abbrev Theory (L : Language) := Set (Sentence L)

instance : Entailment (Theory L) (Sentence L) := ⟨fun T φ ↦ PLift (φ ∈ T)⟩

def Schema.theory (𝓢 : Schema L) : Theory L := {φ | 𝓢 ⊢ ↑φ}

namespace Theory

variable {T : Theory L}

lemma provable_def {φ : Sentence L} : T ⊢ φ ↔ φ ∈ T :=
  ⟨fun h ↦ PLift.down h.some, fun h ↦ ⟨⟨h⟩⟩⟩

@[simp] lemma schema_theory_def {𝓢 : Schema L} {φ : Sentence L} :
    𝓢.theory ⊢ φ ↔ 𝓢 ⊢ ↑φ := by simp [provable_def, Schema.theory]

end Theory

end LO.SecondOrder

end
