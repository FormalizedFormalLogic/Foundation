module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s φ` formula is, over models of `𝗣𝗔`, equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level, and this
equivalence is provable in `𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.Peano

variable {Γ : Polarity} {s n : ℕ}

lemma exists_strictHierarchy_provable {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv (T := 𝗣𝗔) h inferInstance;
  use ψ;

lemma exists_strictHierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end LO.FirstOrder.Arithmetic.Peano
