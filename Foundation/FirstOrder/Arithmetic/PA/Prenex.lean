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

variable {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma hasPrenex (h : Hierarchy Γ s φ) :
    ∃ π : Prenex Γ s Empty n, 𝗣𝗔 ⊢ ∀¹* (φ 🡘 π.val) :=
  Arithmetic.hasPrenex h

lemma exists_matrix_provable (h : Hierarchy Γ s φ) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), 𝗣𝗔 ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨π, hπ⟩ := hasPrenex h;
  exact ⟨π.matrix, hπ⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy Γ s σ) :
    ∃ π₀ : 𝚺₀.Semisentence (0 + s), 𝗣𝗔 ⊢ σ 🡘 π₀.val.toPrenex Γ s :=
  exists_matrix_provable h

lemma exists_hierarchy_provable_of_sentence (h : Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨π, hπ⟩ := hasPrenex h;
  exact ⟨π.sigmaInv.val, π.sigmaInv.val_hierarchy, Prenex.provable_iff_sigmaInv hπ⟩

lemma exists_hierarchy_provable_of_sentence_pi (h : Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  obtain ⟨π, hπ⟩ := hasPrenex h;
  exact ⟨π.piInv.val, π.piInv.val_hierarchy, Prenex.provable_iff_piInv hπ⟩

end LO.FirstOrder.Arithmetic.Peano
