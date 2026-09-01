module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s` formula is `𝗣𝗔`-provably equivalent to an alternating quantifier prefix
over a bounded matrix.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.Peano

variable {Γ : Polarity} {s n : ℕ}

lemma nonempty_prenexNormalForm {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    Nonempty (ArithmeticSemisentence.PrenexNormalForm 𝗣𝗔 Γ s φ) :=
  Arithmetic.nonempty_prenexNormalForm h

lemma exists_matrix_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ φ₀ : ArithmeticSemisentence (n + s),
      Hierarchy 𝚺 0 φ₀ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 φ₀.toPrenex Γ s) := by
  obtain ⟨φ'⟩ := nonempty_prenexNormalForm h;
  exact ⟨φ'.matrix, φ'.matrix_Δ₀, φ'.provable⟩

lemma exists_matrix_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π₀ : ArithmeticSemisentence (0 + s),
      Hierarchy 𝚺 0 π₀ ∧ 𝗣𝗔 ⊢ σ 🡘 π₀.toPrenex Γ s :=
  exists_matrix_provable h

lemma exists_hierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨σ'⟩ := nonempty_prenexNormalForm h;
  exact ⟨↑σ'.sigmaInv, σ'.sigmaInv.hierarchy, σ'.provable_sigmaInv⟩

lemma exists_hierarchy_provable_of_sentence_pi {σ : ArithmeticSentence} (h : Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  obtain ⟨σ'⟩ := nonempty_prenexNormalForm h;
  exact ⟨↑σ'.piInv, σ'.piInv.hierarchy, σ'.provable_piInv⟩

end LO.FirstOrder.Arithmetic.Peano
