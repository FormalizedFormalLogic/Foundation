module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `ℬ[<, ℒₒᵣ].Hierarchy Γ s` formula is `𝗣𝗔`-provably equivalent to an alternating
quantifier prefix
over a bounded matrix.
-/

@[expose] public section

open FFL
open FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic.Peano

variable {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma exists_hierarchy_provable_of_sentence (h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy 𝗣𝗔 h;
  exact ⟨φ'.sigmaInv.val, φ'.sigmaInv.val_hierarchy, Bounding.Prenex.provable_iff_sigmaInv hφ'⟩

lemma exists_hierarchy_provable_of_sentence_pi (h : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy 𝗣𝗔 h;
  exact ⟨φ'.piInv.val, φ'.piInv.val_hierarchy, Bounding.Prenex.provable_iff_piInv hφ'⟩

end FFL.FirstOrder.Arithmetic.Peano
