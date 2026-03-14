module

public import Foundation.Modal.Entailment.Basic
public import Foundation.Meta.ClProver
public import Foundation.Meta.IntProver

namespace LO

section

variable {F : Type*} [DecidableEq F] {S : Type*} [LogicalConnective F] [Entailment S F]

variable {𝓢 𝓣 : S} [Entailment.Cl 𝓢] {φ ψ χ ξ p q r s : F}

example : Entailment.TwoSided 𝓢 [φ, ψ] [χ ⋏ ξ, χ, ψ] := by cl_prover_2s

example : Entailment.TwoSided 𝓢 [φ 🡘 ψ] [φ 🡒 (χ ⋎ ψ)] := by cl_prover_2s

example : Entailment.TwoSided 𝓢 [φ 🡘 ψ, χ 🡘 ξ] [(ψ 🡒 ξ) 🡘 (φ 🡒 χ)] := by cl_prover_2s 12

example (h1 : 𝓢 ⊢ φ 🡘 ψ) (h2 : 𝓢 ⊢ χ 🡘 ξ) : Entailment.TwoSided 𝓢 [] [(ψ 🡒 ξ) 🡘 (φ 🡒 χ)] := by cl_prover_2s [h1, h2]

example : 𝓢 ⊢ (φ ⋏ ψ) 🡒 ((φ 🡒 ψ 🡒 ⊥) 🡒 ⊥) := by cl_prover

example(h1 : 𝓢 ⊢ φ 🡘 ψ) (h2 : 𝓢 ⊢ χ 🡘 ξ) : 𝓢 ⊢ (ψ 🡒 ∼ξ) 🡘 (φ 🡒 ∼χ) := by cl_prover [h1, h2]

example : 𝓢 ⊢ (φ 🡒 ψ) ⋎ (ψ 🡒 φ) := by cl_prover

example : 𝓢 ⊢ ((p ⋎ ∼q) ⋎ ((q ⋎ ∼s) ⋏ (r ⋎ ∼p)))  := by cl_prover

example : 𝓢 ⊢ (((p 🡒 q) 🡒 q) 🡒 p 🡒 q) 🡒 p 🡒 q := by cl_prover

example : 𝓢 ⊢ (p 🡒 ∼q) ⋏ (q ⋎ r) ⋏ p 🡒 r := by cl_prover

example : 𝓢 ⊢ p ⋏ ∼q 🡒 q 🡒 p := by cl_prover

end

section

open LO.Modal.Entailment

variable {S F : Type*} [DecidableEq F] [BasicModalLogicalConnective F] [Entailment S F]

variable {𝓢 𝓣 𝓤 : S} [𝓣 ⪯ 𝓢] [𝓤 ⪯ 𝓢] [Modal.Entailment.K 𝓢] {φ ψ ξ χ : F}

example : 𝓢 ⊢ ((□φ 🡒 □□φ) 🡒 □φ) 🡒 □φ := by cl_prover 6

example (h₁ : 𝓣 ⊢ □φ 🡘 φ) (h₂ : 𝓤 ⊢ □ψ 🡘 ψ) : 𝓢 ⊢ φ ⋎ □ψ 🡘 □φ ⋏ φ ⋎ ψ := by cl_prover [h₁, h₂]

end

section

variable {F : Type*} [DecidableEq F] {S : Type*} [LogicalConnective F] [Entailment S F]

variable {𝓢 𝓣 : S} [Entailment.Int 𝓢] [𝓣 ⪯ 𝓢] {φ ψ χ ξ : F}

example (h : 𝓣 ⊢ φ 🡘 ψ) : 𝓢 ⊢ φ 🡒 (χ ⋎ ψ) := by int_prover [h]

example (h : 𝓣 ⊢ φ 🡘 ψ) : 𝓢 ⊢ (φ ⋏ ∼ψ) 🡘 (ψ ⋏ ∼φ) := by int_prover 64 [h]

example (h : 𝓣 ⊢ φ 🡘 ψ) : 𝓢 ⊢ (φ 🡒 ∼(ψ 🡒 φ)) 🡒 (ψ 🡒 ∼(φ 🡒 ψ)) := by int_prover [h]

end

end LO
