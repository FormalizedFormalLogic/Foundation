import Foundation.IntFO.Basic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language} {T : Theory L}

structure Hilbertᵢ (L : Language) where
  axiomSet : Set (SyntacticFormulaᵢ L)
  shift_closed {φ : SyntacticFormulaᵢ L} : φ ∈ axiomSet → Rewriting.shift φ ∈ axiomSet

instance : SetLike (Hilbertᵢ L) (SyntacticFormulaᵢ L) where
  coe := Hilbertᵢ.axiomSet
  coe_injective' := by rintro ⟨T, _⟩ ⟨U, _⟩; simp

inductive HilbertProofᵢ (Λ : Hilbertᵢ L) : SyntacticFormulaᵢ L → Type _
  | eaxm {φ}       : φ ∈ Λ → HilbertProofᵢ Λ φ
  | mdp {φ ψ}      : HilbertProofᵢ Λ (φ ➝ ψ) → HilbertProofᵢ Λ φ → HilbertProofᵢ Λ ψ
  | gen {φ}        : HilbertProofᵢ Λ (Rewriting.free φ) → HilbertProofᵢ Λ (∀' φ)
  | verum          : HilbertProofᵢ Λ ⊤
  | imply₁ φ ψ     : HilbertProofᵢ Λ (φ ➝ ψ ➝ φ)
  | imply₂ φ ψ χ   : HilbertProofᵢ Λ ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)
  | and₁ φ ψ       : HilbertProofᵢ Λ (φ ⋏ ψ ➝ φ)
  | and₂ φ ψ       : HilbertProofᵢ Λ (φ ⋏ ψ ➝ ψ)
  | and₃ φ ψ       : HilbertProofᵢ Λ (φ ➝ ψ ➝ φ ⋏ ψ)
  | or₁ φ ψ        : HilbertProofᵢ Λ (φ ➝ φ ⋎ ψ)
  | or₂ φ ψ        : HilbertProofᵢ Λ (ψ ➝ φ ⋎ ψ)
  | or₃ φ ψ χ      : HilbertProofᵢ Λ ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ))
  | specialize φ t : HilbertProofᵢ Λ (∀' φ ➝ φ/[t])
  | univk φ ψ      : HilbertProofᵢ Λ (∀' (φ ➝ ψ) ➝ ∀' φ ➝ ∀' ψ)
  | dummy φ        : HilbertProofᵢ Λ (φ ➝ ∀' φ/[])

instance : System (SyntacticFormulaᵢ L) (Hilbertᵢ L) := ⟨HilbertProofᵢ⟩

namespace HilbertProofᵢ

open System.FiniteContext Rewriting LawfulRewriting

variable (Λ : Hilbertᵢ L)

instance : System.ModusPonens Λ := ⟨mdp⟩

instance : System.HasAxiomAndInst Λ := ⟨and₃⟩

instance : System.HasAxiomImply₁ Λ := ⟨imply₁⟩

instance : System.HasAxiomImply₂ Λ := ⟨imply₂⟩

instance : System.Minimal Λ where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  neg_equiv _ := System.iffId _

def forallDummyImply [L.DecidableEq] (φ ψ) : Λ ⊢ ∀' (φ/[] ➝ ψ) ➝ φ ➝ ∀' ψ := deduct' <| deduct <|
  let d₁ : [φ, ∀' (φ/[] ➝ ψ)] ⊢[Λ] ∀' φ/[] ➝ ∀' ψ := of (univk (φ/[]) ψ) ⨀ byAxm₁
  let d₂ : [φ, ∀' (φ/[] ➝ ψ)] ⊢[Λ] ∀' φ/[] := of (dummy φ) ⨀ byAxm₀
  d₁ ⨀ d₂

variable {Λ}

def genOverContextAux [L.DecidableEq] {φ ψ} (b : Λ ⊢ shift φ ➝ free ψ) : Λ ⊢ φ ➝ ∀' ψ :=
  have : Λ ⊢ ∀' (φ/[] ➝ ψ) := gen <| by simpa using b
  forallDummyImply Λ φ ψ ⨀ this

def genOverFiniteContext [L.DecidableEq] {Γ φ} (b : Γ⁺ ⊢[Λ] free φ) : Γ ⊢[Λ] ∀' φ :=
  ofDef <| genOverContextAux <| by simpa [shift_conj₂] using toDef b

end HilbertProofᵢ

end LO.FirstOrder
