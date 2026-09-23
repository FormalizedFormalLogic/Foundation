module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local

@[expose] public section
/-!
# Uniform reflection principles for arithmetic theories

The uniform reflection schema `RFN_Γ(T)` of an arithmetic theory, over formulas of arbitrary arity.

## References

- [Lin97, §4.1, p. 52]
- [AB05, §4.2]
-/

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping.Arithmetic

noncomputable def _root_.FFL.FirstOrder.Theory.globalReflectionSchema
    (T : ArithmeticTheory) [T.Δ₁] {k : ℕ} (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* ∀¹ ((Rew.subst (#0 :> (↑(Encodable.encode φ) : Semiterm ℒₒᵣ Empty (k + 1)) :>
      fun i : Fin k ↦ #i.succ) ▹ (ssnums (k := k)).val) 🡒
    (Rew.subst ![#0] ▹ T.standardProvability.prov 🡒 Rew.bShift ▹ φ))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma models_globalReflectionSchema_iff (T : ArithmeticTheory) [T.Δ₁] {k : ℕ}
    (φ : ArithmeticSemisentence k) :
    V ⊧/![] (T.globalReflectionSchema φ) ↔
      ∀ v : Fin k → V, Bootstrapping.Provable T (substNumerals (⌜φ⌝ : V) v) → V ⊧/v φ := by
  simp [Theory.globalReflectionSchema, Sentence.quote_eq_encode, numeral_eq_natCast];

noncomputable def _root_.FFL.FirstOrder.Theory.uniformReflectionOn
    (T : ArithmeticTheory) [T.Δ₁] (Γ : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop) :
    Set ArithmeticSentence :=
  { σ | ∃ (k : ℕ) (φ : ArithmeticSemisentence k), Γ φ ∧ σ = T.globalReflectionSchema φ }

@[inherit_doc] notation "𝗥𝗙𝗡[" Γ "] " T:max => Theory.uniformReflectionOn T Γ

variable {T : ArithmeticTheory} [T.Δ₁]

@[simp]
lemma mem_uniformReflectionOn_iff {Γ : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop}
    {σ : ArithmeticSentence} :
    σ ∈ T.uniformReflectionOn Γ ↔
      ∃ (k : ℕ) (φ : ArithmeticSemisentence k), Γ φ ∧ σ = T.globalReflectionSchema φ := Iff.rfl

lemma uniformReflectionOn_mono {Γ Γ' : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop}
    (h : ∀ {k : ℕ} (φ : ArithmeticSemisentence k), Γ φ → Γ' φ) :
    T.uniformReflectionOn Γ ⊆ T.uniformReflectionOn Γ' := by
  rintro σ ⟨k, φ, hφ, rfl⟩;
  exact ⟨k, φ, h φ hφ, rfl⟩;

end FFL.FirstOrder.Arithmetic
