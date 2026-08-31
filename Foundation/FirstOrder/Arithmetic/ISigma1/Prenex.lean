module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv

/-!
# Prenex normal form theorem over $\mathsf{I\Sigma_1}$

Every `Hierarchy 𝚺 1` formula is `𝗜𝚺₁`-provably equivalent to a formula of the form `∃¹ θ`
with `θ` in `Hierarchy 𝚺 0`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.ISigma1

variable {n : ℕ}

lemma nonempty_strictEquiv {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    Nonempty (StrictEquiv 𝗜𝚺₁ 𝚺 1 φ) :=
  Arithmetic.nonempty_strictEquiv h inferInstance

lemma exists_strictHierarchy_provable {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv h;
  obtain ⟨θ, rfl, hθ⟩ := ψ_hie.sigma_succ_elim;
  use θ;
  and_intros;
  . exact StrictHierarchy.zero_iff.mp hθ;
  . assumption;

lemma exists_strictHierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy 𝚺 1 σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ :=
  exists_strictHierarchy_provable h

end LO.FirstOrder.Arithmetic.ISigma1
