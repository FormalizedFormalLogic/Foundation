module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-!
# Alternating quantifier prefixes and the Δ₀-kernel of a strict hierarchy formula

`Polarity.quantItr Γ s` prepends the length-`s` alternating quantifier prefix starting
with `Γ` (`∃¹` if `Γ = 𝚺`, `∀¹` if `Γ = 𝚷`, then alternating). `strictHierarchy_iff_exists_kernel`
shows that `StrictHierarchy Γ s ψ` holds iff `ψ = quantItr Γ s φ` for some `Δ₀` kernel `φ`.
-/

@[expose] public section
namespace LO.Polarity

variable {α : ℕ → Type*} [FirstOrder.UnivQuantifier α] [FirstOrder.ExsQuantifier α] {n : ℕ} {Γ : Polarity}

def quant : Polarity → α (n + 1) → α n
  | 𝚺 => FirstOrder.ExsQuantifier.exs
  | 𝚷 => FirstOrder.UnivQuantifier.all

@[simp] lemma quant_sigma (φ : α (n + 1)) : (𝚺 : Polarity).quant φ = ∃¹ φ := rfl

@[simp] lemma quant_pi (φ : α (n + 1)) : (𝚷 : Polarity).quant φ = ∀¹ φ := rfl

def quantItr (Γ : Polarity) : (k : ℕ) → α (n + k) → α n
  | 0,     φ => φ
  | k + 1, φ => quantItr Γ k ((Polarity.alt^[k] Γ).quant φ)

@[simp]
lemma quantItr_zero (φ : α n) : quantItr Γ 0 φ = φ := rfl

lemma quantItr_succ {k} (φ : α (n + (k + 1))) :
    quantItr Γ (k + 1) φ = quantItr Γ k ((Polarity.alt^[k] Γ).quant φ) := rfl

end LO.Polarity

namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s j n : ℕ}

example {φ₀ : Semiformula L ξ (n + 2)} : Polarity.quantItr 𝚺 2 φ₀ = ∃¹ ∀¹ φ₀ := rfl

example {φ₀ : Semiformula L ξ (n + 1)} : Polarity.quantItr 𝚺 1 φ₀ = ∃¹ φ₀ := rfl

lemma strictHierarchy_quantItr {φ : Semiformula L ξ (n + s)}
    (h : StrictHierarchy (Polarity.alt^[s] Γ) j φ) :
    StrictHierarchy Γ (s + j) (Polarity.quantItr Γ s φ) := by
  induction s generalizing n j with
  | zero => simpa using h;
  | succ s ih =>
    rw [Function.iterate_succ_apply'] at h;
    have e : s + (j + 1) = s + 1 + j := by omega;
    rw [Polarity.quantItr_succ, ← e];
    rcases hΓ : Polarity.alt^[s] Γ with _ | _;
    . refine ih ?_;
      rw [hΓ] at h ⊢;
      exact StrictHierarchy.sigma h;
    . refine ih ?_;
      rw [hΓ] at h ⊢;
      exact StrictHierarchy.pi h;

lemma exists_kernel {ψ : Semiformula L ξ n} (h : StrictHierarchy Γ (s + j) ψ) :
    ∃ φ : Semiformula L ξ (n + s), StrictHierarchy (Polarity.alt^[s] Γ) j φ ∧ ψ = Polarity.quantItr Γ s φ := by
  induction s generalizing n j with
  | zero => exact ⟨ψ, by simpa using h, rfl⟩;
  | succ s ih =>
    have e : s + 1 + j = s + (j + 1) := by omega;
    rw [e] at h;
    obtain ⟨φ', hφ', rfl⟩ := ih h;
    rcases hΓ : Polarity.alt^[s] Γ with _ | _;
    . rw [hΓ] at hφ';
      obtain ⟨φ'', rfl, hφ''⟩ := StrictHierarchy.sigma_succ_elim hφ';
      use φ'';
      and_intros;
      . rw [Function.iterate_succ_apply', hΓ];
        exact hφ'';
      . rw [Polarity.quantItr_succ, hΓ]; rfl;
    . rw [hΓ] at hφ';
      obtain ⟨φ'', rfl, hφ''⟩ := StrictHierarchy.pi_succ_elim hφ';
      use φ'';
      and_intros;
      . rw [Function.iterate_succ_apply', hΓ];
        exact hφ'';
      . rw [Polarity.quantItr_succ, hΓ]; rfl;

theorem strictHierarchy_iff_exists_kernel {ψ : Semiformula L ξ n} :
    StrictHierarchy Γ s ψ ↔ ∃ φ : Semiformula L ξ (n + s), Hierarchy 𝚺 0 φ ∧ ψ = Polarity.quantItr Γ s φ := by
  constructor;
  . intro h;
    obtain ⟨φ, hφ, rfl⟩ := exists_kernel (j := 0) h;
    exact ⟨φ, StrictHierarchy.zero_iff.mp hφ, rfl⟩;
  . rintro ⟨φ, hφ, rfl⟩;
    exact strictHierarchy_quantItr (StrictHierarchy.zero hφ);

end LO.FirstOrder.Arithmetic
