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
    ∃ φ' : Prenex Γ s Empty n, 𝗣𝗔 ⊢ ∀¹* (φ 🡘 φ'.val) :=
  exists_prenex_of_hierarchy 𝗣𝗔 h

lemma exists_matrix_provable (h : Hierarchy Γ s φ) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), 𝗣𝗔 ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h;
  exact ⟨φ'.matrix, hφ'⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy Γ s σ) :
    ∃ φ₀ : 𝚺₀.Semisentence (0 + s), 𝗣𝗔 ⊢ σ 🡘 φ₀.val.toPrenex Γ s :=
  exists_matrix_provable h

lemma exists_hierarchy_provable_of_sentence (h : Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h;
  exact ⟨φ'.sigmaInv.val, φ'.sigmaInv.val_hierarchy, Prenex.provable_iff_sigmaInv hφ'⟩

lemma exists_hierarchy_provable_of_sentence_pi (h : Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h;
  exact ⟨φ'.piInv.val, φ'.piInv.val_hierarchy, Prenex.provable_iff_piInv hφ'⟩

end LO.FirstOrder.Arithmetic.Peano
