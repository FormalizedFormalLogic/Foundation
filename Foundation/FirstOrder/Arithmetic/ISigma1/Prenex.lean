module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Prenex normal form theorem over $\mathsf{I\Sigma_1}$

Every `Hierarchy 𝚺 1` formula is `𝗜𝚺₁`-provably equivalent to a formula of the form `∃¹ θ`
with `θ` in `Hierarchy 𝚺 0`, and dually for `Hierarchy 𝚷 1` and `∀¹ θ`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.ISigma1

variable {n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma hasPrenex (h : Hierarchy 𝚺 1 φ) :
    ∃ π : Prenex 𝚺 1 Empty n, 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 π.val) :=
  Arithmetic.hasPrenex h

lemma exists_matrix_provable (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  obtain ⟨π, hπ⟩ := hasPrenex h;
  exact ⟨π.sigmaInv.val, π.sigmaInv.val_deltaZero, Prenex.provable_iff_sigmaInv hπ⟩

lemma exists_matrix_provable_pi (h : Hierarchy 𝚷 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∀¹ θ) := by
  obtain ⟨π, hπ⟩ := Arithmetic.hasPrenex (T := 𝗜𝚺₁) h
  exact ⟨π.piInv.val, π.piInv.val_hierarchy, Prenex.provable_iff_piInv hπ⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy 𝚺 1 σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ :=
  exists_matrix_provable h

end LO.FirstOrder.Arithmetic.ISigma1
