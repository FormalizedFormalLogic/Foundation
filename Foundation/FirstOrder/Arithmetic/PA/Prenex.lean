module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s` formula is `𝗣𝗔`-provably equivalent to an alternating quantifier prefix
over a bounded kernel.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic.Peano

variable {Γ : Polarity} {s n : ℕ}

lemma nonempty_strictHierarchyFormulaEquivOf {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    Nonempty (StrictHierarchyFormulaEquivOf 𝗣𝗔 Γ s φ) :=
  Arithmetic.nonempty_strictHierarchyFormulaEquivOf h inferInstance

lemma exists_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ φ₀ : ArithmeticSemisentence (n + s),
      Hierarchy 𝚺 0 φ₀ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀) := by
  obtain ⟨φ'⟩ := nonempty_strictHierarchyFormulaEquivOf h;
  exact ⟨φ'.kernel, φ'.kernel_deltaZero, φ'.provable⟩

lemma exists_kernel_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π₀ : ArithmeticSemisentence (0 + s),
      Hierarchy 𝚺 0 π₀ ∧ 𝗣𝗔 ⊢ σ 🡘 Polarity.quantItr Γ s π₀ :=
  exists_kernel_provable h

lemma exists_hierarchy_provable_of_sentence {σ : ArithmeticSentence} (h : Hierarchy 𝚺 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚷 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨σ'⟩ := nonempty_strictHierarchyFormulaEquivOf h;
  use ↑σ'.sigmaInv;
  and_intros;
  . exact σ'.sigmaInv.hierarchy;
  . have hprov := σ'.provable;
    rw [σ'.coe_sigmaInv] at hprov;
    exact hprov;

lemma exists_hierarchy_provable_of_sentence_pi {σ : ArithmeticSentence} (h : Hierarchy 𝚷 (s + 1) σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 s θ ∧ 𝗣𝗔 ⊢ σ 🡘 ∀¹ θ := by
  obtain ⟨σ'⟩ := nonempty_strictHierarchyFormulaEquivOf h;
  use ↑σ'.piInv;
  and_intros;
  . exact σ'.piInv.hierarchy;
  . have hprov := σ'.provable;
    rw [σ'.coe_piInv] at hprov;
    exact hprov;

end LO.FirstOrder.Arithmetic.Peano
