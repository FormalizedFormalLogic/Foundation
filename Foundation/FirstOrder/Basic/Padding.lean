import Foundation.FirstOrder.Basic.Semantics.Semantics
import Foundation.FirstOrder.Basic.Calculus
import Foundation.Propositional.Entailment.Cl.Basic

namespace LO.FirstOrder

variable {L : Language} {ξ : Type*}

namespace Semiformula

def padding (φ : Semiformula L ξ n) (k : ℕ) := φ ⋏ (List.replicate k ⊤).conj

def getPaddingAux : Semiformula L ξ n → Option ℕ
  |     ⊤ => some 0
  | ⊤ ⋏ φ => φ.getPaddingAux.map fun x ↦ x + 1
  |     _ => none

def getPadding : Semiformula L ξ n → Option ℕ
  | _ ⋏ φ => φ.getPaddingAux
  |     _ => none

def getPaddingFormula : Semiformula L ξ n → Option (Semiformula L ξ n)
  | φ ⋏ _ => some φ
  |     _ => none

@[simp] lemma getPadding_padding (φ : Semiformula L ξ n) : (φ.padding k).getPadding = some k := by
  suffices (List.replicate k (⊤ : Semiformula L ξ n)).conj.getPaddingAux = some k by simpa [getPadding, padding]
  induction k <;> simp [List.replicate_succ, getPaddingAux, *]

@[simp] lemma getPaddingFormula_padding (φ : Semiformula L ξ n) : (φ.padding k).getPaddingFormula = some φ := by
  simp [padding, getPaddingFormula]

@[simp] lemma padding_injective_iff {φ ψ : Semiformula L ξ n} :
    φ.padding k = ψ.padding m ↔ φ = ψ ∧ k = m :=
  ⟨fun h ↦ ⟨by simpa using congr_arg getPaddingFormula h, by simpa using congr_arg getPadding h⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

@[simp] lemma rew_padding (ω : Rew L ξ n ξ' n') (φ : Semiformula L ξ n) :
    ω ▹ φ.padding k = (ω ▹ φ).padding k := by
  simp [padding]
  induction k <;> simp [List.replicate_succ, *]

end Semiformula

open Entailment

def Entailment.paddingIff [L.DecidableEq] [DecidableEq ξ] [Entailment S (Formula L ξ)] {𝓢 : S} [Entailment.Minimal 𝓢] (φ k) :
    𝓢 ⊢! φ.padding k ⭤ φ := by
  apply E_intro
  · apply and₁
  · apply right_K_intro
    · apply C_id
    · apply dhyp
      apply Conj_intro
      intro φ hφ
      have : k ≠ 0 ∧ φ = ⊤ := by simpa using hφ
      exact Entailment.cast this.2.symm HasAxiomVerum.verum

@[simp] def Entailment.padding_iff [L.DecidableEq] [DecidableEq ξ] [Entailment S (Formula L ξ)] {𝓢 : S} [Entailment.Minimal 𝓢] (φ k) :
    𝓢 ⊢ φ.padding k ⭤ φ := ⟨paddingIff φ k⟩

end LO.FirstOrder
