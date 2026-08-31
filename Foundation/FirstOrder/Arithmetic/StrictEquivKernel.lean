module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchyKernel
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# `Δ₀`-kernel form of `T`-provable strict hierarchy equivalence

`exists_kernel_provable` repackages `nonempty_strictEquiv` (`StrictEquiv.lean`) via
`strictHierarchy_iff_exists_kernel` (`Basic/StrictHierarchyKernel.lean`), producing a `Δ₀` kernel
`φ₀` together with the alternating quantifier prefix `Polarity.quantItr Γ s φ₀` directly, instead
of a `StrictHierarchy Γ s` witness.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} {Γ : Polarity} {s n : ℕ}

theorem exists_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) :
    ∃ φ₀ : ArithmeticSemisentence (n + s),
      Hierarchy 𝚺 0 φ₀ ∧ T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans inferInstance (ISigma_weakerThan_of_le_trans (Nat.zero_le s) hT);
  obtain ⟨⟨ψ, hψ, hprov⟩⟩ := nonempty_strictEquiv h hT;
  obtain ⟨φ₀, hφ₀, rfl⟩ := strictHierarchy_iff_exists_kernel.mp hψ;
  exact ⟨φ₀, hφ₀, hprov⟩;

theorem exists_kernel_provable' {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀.val) := by
  obtain ⟨φ₀, hφ₀, hprov⟩ := exists_kernel_provable h hT;
  exact ⟨.mkSigma φ₀ hφ₀, by simpa using hprov⟩;

namespace ISigma1

lemma exists_delta0_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  obtain ⟨θ, hθ, hprov⟩ := exists_kernel_provable h (inferInstance : 𝗜𝚺 1 ⪯ 𝗜𝚺₁);
  exact ⟨θ, hθ, hprov⟩;

lemma exists_delta0_kernel_provable_pi {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚷 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∀¹ θ) := by
  obtain ⟨θ, hθ, hprov⟩ := exists_kernel_provable h (inferInstance : 𝗜𝚺 1 ⪯ 𝗜𝚺₁);
  exact ⟨θ, hθ, hprov⟩;

end ISigma1

end LO.FirstOrder.Arithmetic
