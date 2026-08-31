module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s` formula is `𝗣𝗔`-provably equivalent to a formula in `StrictHierarchy Γ s`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.Peano

variable {Γ : Polarity} {s n : ℕ}

lemma nonempty_strictEquiv {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    Nonempty (StrictEquiv 𝗣𝗔 Γ s φ) :=
  Arithmetic.nonempty_strictEquiv h inferInstance

lemma exists_strictHierarchy_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemisentence n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv h;
  use ψ;

lemma exists_strictHierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π :=
  exists_strictHierarchy_provable h

lemma exists_hierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv h;
  obtain ⟨θ, rfl, hθ⟩ := ψ_hie.sigma_succ_elim;
  use θ;
  and_intros;
  . exact hθ.hierarchy;
  . assumption;

lemma exists_hierarchy_provable_of_sentence_pi {σ : ArithmeticSentence} (h : Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv h;
  obtain ⟨θ, rfl, hθ⟩ := ψ_hie.pi_succ_elim;
  use θ;
  and_intros;
  . exact hθ.hierarchy;
  . assumption;

end LO.FirstOrder.Arithmetic.Peano
