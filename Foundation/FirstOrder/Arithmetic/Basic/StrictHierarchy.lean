module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-!
# Strict arithmetical hierarchy formulas

A strict hierarchy formula stores its bounded kernel together with its alternating
quantifier prefix.
-/

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

structure StrictHierarchyFormula (L : Language) [L.LT] (ξ : Type*) (Γ : Polarity) (s n : ℕ) where
  kernel : Semiformula L ξ (n + s)
  kernel_deltaZero : Hierarchy 𝚺 0 kernel

namespace StrictHierarchyFormula

variable {ξ : Type*} {Γ : Polarity} {s n : ℕ}

@[coe] def val (φ : StrictHierarchyFormula L ξ Γ s n) : Semiformula L ξ n :=
  Polarity.quantItr Γ s φ.kernel

instance : CoeTC (StrictHierarchyFormula L ξ Γ s n) (Semiformula L ξ n) := ⟨val⟩

@[ext] lemma ext {φ ψ : StrictHierarchyFormula L ξ Γ s n} (h : φ.kernel = ψ.kernel) : φ = ψ := by
  cases φ
  cases ψ
  simp_all

@[simp] lemma val_mk (φ : Semiformula L ξ (n + s)) (h : Hierarchy 𝚺 0 φ) :
    (⟨φ, h⟩ : StrictHierarchyFormula L ξ Γ s n).val = Polarity.quantItr Γ s φ := rfl

def zero (Γ : Polarity) (φ : Semiformula L ξ n) (h : Hierarchy 𝚺 0 φ) :
    StrictHierarchyFormula L ξ Γ 0 n := ⟨φ, h⟩

def sigma (φ : StrictHierarchyFormula L ξ 𝚷 s (n + 1)) :
    StrictHierarchyFormula L ξ 𝚺 (s + 1) n :=
  ⟨Rew.castLE (Nat.succ_add n s).le ▹ φ.kernel, φ.kernel_deltaZero.rew _⟩

def pi (φ : StrictHierarchyFormula L ξ 𝚺 s (n + 1)) :
    StrictHierarchyFormula L ξ 𝚷 (s + 1) n :=
  ⟨Rew.castLE (Nat.succ_add n s).le ▹ φ.kernel, φ.kernel_deltaZero.rew _⟩

def sigmaInv (φ : StrictHierarchyFormula L ξ 𝚺 (s + 1) n) :
    StrictHierarchyFormula L ξ 𝚷 s (n + 1) :=
  ⟨Rew.castLE (Nat.succ_add n s).ge ▹ φ.kernel, φ.kernel_deltaZero.rew _⟩

def piInv (φ : StrictHierarchyFormula L ξ 𝚷 (s + 1) n) :
    StrictHierarchyFormula L ξ 𝚺 s (n + 1) :=
  ⟨Rew.castLE (Nat.succ_add n s).ge ▹ φ.kernel, φ.kernel_deltaZero.rew _⟩

def neg (φ : StrictHierarchyFormula L ξ Γ s n) : StrictHierarchyFormula L ξ Γ.alt s n :=
  ⟨∼φ.kernel, φ.kernel_deltaZero.neg.of_zero⟩

def rew (φ : StrictHierarchyFormula L ξ₁ Γ s n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchyFormula L ξ₂ Γ s n₂ :=
  ⟨ω.qpow s ▹ φ.kernel, φ.kernel_deltaZero.rew _⟩

@[simp] lemma coe_zero (Γ : Polarity) (φ : Semiformula L ξ n) (h : Hierarchy 𝚺 0 φ) :
    (↑(zero Γ φ h) : Semiformula L ξ n) = φ := rfl

@[simp] lemma coe_sigma (φ : StrictHierarchyFormula L ξ 𝚷 s (n + 1)) :
    (↑φ.sigma : Semiformula L ξ n) = ∃¹ (↑φ : Semiformula L ξ (n + 1)) := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]

@[simp] lemma coe_pi (φ : StrictHierarchyFormula L ξ 𝚺 s (n + 1)) :
    (↑φ.pi : Semiformula L ξ n) = ∀¹ (↑φ : Semiformula L ξ (n + 1)) := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]

lemma coe_sigmaInv (φ : StrictHierarchyFormula L ξ 𝚺 (s + 1) n) :
    (↑φ : Semiformula L ξ n) = ∃¹ (↑φ.sigmaInv : Semiformula L ξ (n + 1)) := by
  change Polarity.quantItr 𝚺 (s + 1) φ.kernel =
    (𝚺 : Polarity).quant (Polarity.quantItr (𝚺 : Polarity).alt s (Rew.castLE _ ▹ φ.kernel))
  rw [← Rewriting.quantItr_succ_smul_castLE]
  rw [← TransitiveRewriting.comp_app]
  simp

lemma coe_piInv (φ : StrictHierarchyFormula L ξ 𝚷 (s + 1) n) :
    (↑φ : Semiformula L ξ n) = ∀¹ (↑φ.piInv : Semiformula L ξ (n + 1)) := by
  change Polarity.quantItr 𝚷 (s + 1) φ.kernel =
    (𝚷 : Polarity).quant (Polarity.quantItr (𝚷 : Polarity).alt s (Rew.castLE _ ▹ φ.kernel))
  rw [← Rewriting.quantItr_succ_smul_castLE]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp] lemma sigmaInv_sigma (φ : StrictHierarchyFormula L ξ 𝚷 s (n + 1)) :
    φ.sigma.sigmaInv = φ := by
  ext
  simp only [sigma, sigmaInv]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp] lemma sigma_sigmaInv (φ : StrictHierarchyFormula L ξ 𝚺 (s + 1) n) :
    φ.sigmaInv.sigma = φ := by
  ext
  simp only [sigma, sigmaInv]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp] lemma piInv_pi (φ : StrictHierarchyFormula L ξ 𝚺 s (n + 1)) : φ.pi.piInv = φ := by
  ext
  simp only [pi, piInv]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp] lemma pi_piInv (φ : StrictHierarchyFormula L ξ 𝚷 (s + 1) n) : φ.piInv.pi = φ := by
  ext
  simp only [pi, piInv]
  rw [← TransitiveRewriting.comp_app]
  simp

@[simp] lemma coe_neg (φ : StrictHierarchyFormula L ξ Γ s n) :
    (↑φ.neg : Semiformula L ξ n) = ∼(↑φ : Semiformula L ξ n) := by
  simp [val, neg]

@[simp] lemma coe_rew (φ : StrictHierarchyFormula L ξ₁ Γ s n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    (↑(φ.rew ω) : Semiformula L ξ₂ n₂) = ω ▹ (↑φ : Semiformula L ξ₁ n₁) := by
  simp [val, rew]

end StrictHierarchyFormula

namespace Hierarchy

variable {ξ : Type*} {Γ : Polarity} {s j n : ℕ}

lemma quantItr {φ : Semiformula L ξ (n + s)}
    (h : Hierarchy (Polarity.alt^[s] Γ) j φ) :
    Hierarchy Γ (j + s) (Polarity.quantItr Γ s φ) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Function.iterate_succ_apply'] at h
    rw [Polarity.quantItr_succ, (show j + (s + 1) = (j + 1) + s by omega)]
    rcases hΓ : Polarity.alt^[s] Γ with _ | _
    . apply ih
      rw [hΓ] at h ⊢
      exact h.sigma
    . apply ih
      rw [hΓ] at h ⊢
      exact h.pi

end Hierarchy

namespace StrictHierarchyFormula

variable {ξ : Type*} {Γ : Polarity} {s n : ℕ}

lemma hierarchy (φ : StrictHierarchyFormula L ξ Γ s n) :
    Hierarchy Γ s (↑φ : Semiformula L ξ n) := by
  change Hierarchy Γ s (Polarity.quantItr Γ s φ.kernel)
  simpa only [Nat.zero_add] using Hierarchy.quantItr (Γ := Γ) (j := 0) φ.kernel_deltaZero.of_zero

@[simp] lemma deltaZero (φ : StrictHierarchyFormula L ξ Γ 0 n) :
    Hierarchy 𝚺 0 (↑φ : Semiformula L ξ n) := by
  change Hierarchy 𝚺 0 (Polarity.quantItr Γ 0 φ.kernel)
  exact φ.kernel_deltaZero

end StrictHierarchyFormula

end LO.FirstOrder.Arithmetic
