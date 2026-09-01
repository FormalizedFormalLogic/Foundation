module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-!
# Strict arithmetical hierarchy prenex forms

A strict hierarchy formula stores its bounded matrix together with its alternating
quantifier prefix.
-/

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

structure Prenex (L : Language) [L.LT] (ξ : Type*) (Γ : Polarity) (s n : ℕ) where
  matrix : Semiformula L ξ (n + s)
  matrix_Δ₀ : Hierarchy 𝚺 0 matrix

namespace Prenex

variable {ξ : Type*} {Γ : Polarity} {s n : ℕ}

@[coe]
def val (φ : Prenex L ξ Γ s n) : Semiformula L ξ n := Polarity.quantItr Γ s φ.matrix

instance : CoeTC (Prenex L ξ Γ s n) (Semiformula L ξ n) := ⟨val⟩

@[ext]
lemma ext {φ ψ : Prenex L ξ Γ s n} (h : φ.matrix = ψ.matrix) : φ = ψ := by
  cases φ; cases ψ; simp_all

@[simp]
lemma val_mk (φ : Semiformula L ξ (n + s)) (φ_Δ₀ : Hierarchy 𝚺 0 φ) :
  (⟨φ, φ_Δ₀⟩ : Prenex L ξ Γ s n).val = Polarity.quantItr Γ s φ := rfl

def zero (Γ : Polarity) (φ : Semiformula L ξ n) (φ_Δ₀ : Hierarchy 𝚺 0 φ) :
    Prenex L ξ Γ 0 n := ⟨φ, φ_Δ₀⟩

def sigma (φ : Prenex L ξ 𝚷 s (n + 1)) :
    Prenex L ξ 𝚺 (s + 1) n :=
  ⟨Rew.castLE (Nat.succ_add n s).le ▹ φ.matrix, φ.matrix_Δ₀.rew _⟩

def pi (φ : Prenex L ξ 𝚺 s (n + 1)) :
    Prenex L ξ 𝚷 (s + 1) n :=
  ⟨Rew.castLE (Nat.succ_add n s).le ▹ φ.matrix, φ.matrix_Δ₀.rew _⟩

def sigmaInv (φ : Prenex L ξ 𝚺 (s + 1) n) :
    Prenex L ξ 𝚷 s (n + 1) :=
  ⟨Rew.castLE (Nat.succ_add n s).ge ▹ φ.matrix, φ.matrix_Δ₀.rew _⟩

def piInv (φ : Prenex L ξ 𝚷 (s + 1) n) :
    Prenex L ξ 𝚺 s (n + 1) :=
  ⟨Rew.castLE (Nat.succ_add n s).ge ▹ φ.matrix, φ.matrix_Δ₀.rew _⟩

def neg (φ : Prenex L ξ Γ s n) : Prenex L ξ Γ.alt s n :=
  ⟨∼φ.matrix, φ.matrix_Δ₀.neg.of_zero⟩

def rew (φ : Prenex L ξ₁ Γ s n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    Prenex L ξ₂ Γ s n₂ :=
  ⟨ω.qpow s ▹ φ.matrix, φ.matrix_Δ₀.rew _⟩

@[simp]
lemma coe_zero (Γ : Polarity) (φ : Semiformula L ξ n) (φ_Δ₀ : Hierarchy 𝚺 0 φ) :
  (↑(zero Γ φ φ_Δ₀) : Semiformula L ξ n) = φ := rfl

@[simp]
lemma coe_sigma (φ : Prenex L ξ 𝚷 s (n + 1)) :
  (↑φ.sigma : Semiformula L ξ n) = ∃¹ (↑φ : Semiformula L ξ (n + 1)) := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]

@[simp]
lemma coe_pi (φ : Prenex L ξ 𝚺 s (n + 1)) :
    (↑φ.pi : Semiformula L ξ n) = ∀¹ (↑φ : Semiformula L ξ (n + 1)) := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]

lemma coe_sigmaInv (φ : Prenex L ξ 𝚺 (s + 1) n) :
    (↑φ : Semiformula L ξ n) = ∃¹ (↑φ.sigmaInv : Semiformula L ξ (n + 1)) := by
  change Polarity.quantItr 𝚺 (s + 1) φ.matrix =
    (𝚺 : Polarity).quant (Polarity.quantItr (𝚺 : Polarity).alt s (Rew.castLE _ ▹ φ.matrix))
  rw [← Rewriting.quantItr_succ_smul_castLE]
  rw [← TransitiveRewriting.comp_app]
  simp

lemma coe_piInv (φ : Prenex L ξ 𝚷 (s + 1) n) :
    (↑φ : Semiformula L ξ n) = ∀¹ (↑φ.piInv : Semiformula L ξ (n + 1)) := by
  change Polarity.quantItr 𝚷 (s + 1) φ.matrix =
    (𝚷 : Polarity).quant (Polarity.quantItr (𝚷 : Polarity).alt s (Rew.castLE _ ▹ φ.matrix))
  rw [← Rewriting.quantItr_succ_smul_castLE]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp]
lemma sigmaInv_sigma (φ : Prenex L ξ 𝚷 s (n + 1)) : φ.sigma.sigmaInv = φ := by
  ext
  simp [sigma, sigmaInv, ← TransitiveRewriting.comp_app]

@[simp]
lemma sigma_sigmaInv (φ : Prenex L ξ 𝚺 (s + 1) n) : φ.sigmaInv.sigma = φ := by
  ext
  simp [sigma, sigmaInv, ← TransitiveRewriting.comp_app]

@[simp]
lemma piInv_pi (φ : Prenex L ξ 𝚺 s (n + 1)) : φ.pi.piInv = φ := by
  ext
  simp [pi, piInv, ← TransitiveRewriting.comp_app]

@[simp]
lemma pi_piInv (φ : Prenex L ξ 𝚷 (s + 1) n) : φ.piInv.pi = φ := by
  ext
  simp [pi, piInv, ← TransitiveRewriting.comp_app]

@[simp]
lemma coe_neg (φ : Prenex L ξ Γ s n) :
    (↑φ.neg : Semiformula L ξ n) = ∼(↑φ : Semiformula L ξ n) := by
  simp [val, neg]

@[simp]
lemma coe_rew (φ : Prenex L ξ₁ Γ s n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    (↑(φ.rew ω) : Semiformula L ξ₂ n₂) = ω ▹ (↑φ : Semiformula L ξ₁ n₁) := by
  simp [val, rew]

end Prenex

namespace Hierarchy

variable {ξ : Type*} {Γ : Polarity} {s j n : ℕ}

lemma quantItr {φ : Semiformula L ξ (n + s)}
    (h : Hierarchy (Γ.altItr s) j φ) :
    Hierarchy Γ (j + s) (Polarity.quantItr Γ s φ) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    rw [Polarity.quantItr_succ, (show j + (s + 1) = (j + 1) + s by omega)]
    rcases hΓ : Γ.altItr s with _ | _
    . apply ih
      rw [hΓ] at h ⊢
      exact h.sigma
    . apply ih
      rw [hΓ] at h ⊢
      exact h.pi

end Hierarchy

namespace Prenex

variable {ξ : Type*} {Γ : Polarity} {s n : ℕ}

lemma hierarchy (φ : Prenex L ξ Γ s n) :
    Hierarchy Γ s (↑φ : Semiformula L ξ n) := by
  change Hierarchy Γ s (Polarity.quantItr Γ s φ.matrix)
  simpa only [Nat.zero_add] using Hierarchy.quantItr (Γ := Γ) (j := 0) φ.matrix_Δ₀.of_zero

@[simp]
lemma deltaZero (φ : Prenex L ξ Γ 0 n) :
    Hierarchy 𝚺 0 (↑φ : Semiformula L ξ n) := by
  change Hierarchy 𝚺 0 (Polarity.quantItr Γ 0 φ.matrix)
  exact φ.matrix_Δ₀

end Prenex

end LO.FirstOrder.Arithmetic
