module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Prenex normal form theorem over $\mathsf{I\Sigma_1}$

Every `Hierarchy 𝚺 1` formula is `𝗜𝚺⁺₁`-provably equivalent to a formula of the form `∃¹ θ`
with `θ` in `Hierarchy 𝚺 0`, and dually for `Hierarchy 𝚷 1` and `∀¹ θ`.
-/

@[expose] public section

open FFL
open FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic.ISigma1

variable {n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma hasPrenex (h : Hierarchy 𝚺 1 φ) :
    ∃ φ' : Prenex 𝚺 1 Empty n, 𝗜𝚺⁺₁ ⊢ ∀¹* (φ 🡘 φ'.val) :=
  exists_prenex_of_hierarchy 𝗜𝚺⁺₁ h

lemma exists_matrix_provable (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : 𝚺₀.Semisentence (n + 1), 𝗜𝚺⁺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ.val) := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h;
  exact ⟨φ'.sigmaInv.matrix, Prenex.provable_iff_sigmaInv hφ'⟩

lemma exists_matrix_provable_pi (h : Hierarchy 𝚷 1 φ) :
    ∃ θ : 𝚺₀.Semisentence (n + 1), 𝗜𝚺⁺₁ ⊢ ∀¹* (φ 🡘 ∀¹ θ.val) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy 𝗜𝚺⁺₁ h
  exact ⟨φ'.piInv.matrix, Prenex.provable_iff_piInv hφ'⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy 𝚺 1 σ) :
    ∃ θ : 𝚺₀.Semisentence 1, 𝗜𝚺⁺₁ ⊢ σ 🡘 ∃¹ θ.val :=
  exists_matrix_provable h

end FFL.FirstOrder.Arithmetic.ISigma1
