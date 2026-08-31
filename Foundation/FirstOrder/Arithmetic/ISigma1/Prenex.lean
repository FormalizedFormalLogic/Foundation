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

lemma nonempty_strictHierarchyFormulaEquivOf {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    Nonempty (StrictHierarchyFormulaEquivOf 𝗜𝚺₁ 𝚺 1 φ) :=
  Arithmetic.nonempty_strictHierarchyFormulaEquivOf h inferInstance

lemma exists_strictHierarchy_provable {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  obtain ⟨φ'⟩ := nonempty_strictHierarchyFormulaEquivOf h;
  use (↑φ'.sigmaInv : ArithmeticSemisentence (n + 1));
  and_intros;
  . exact φ'.sigmaInv.deltaZero;
  . rw [← φ'.coe_sigmaInv];
    exact φ'.provable;

lemma exists_strictHierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy 𝚺 1 σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ :=
  exists_strictHierarchy_provable h

end LO.FirstOrder.Arithmetic.ISigma1
