import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Consistency predicate

-/

open Classical

namespace LO.ISigma1.Metamath

open FirstOrder Arith PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

def _root_.LO.FirstOrder.Theory.Consistencyₐ (φ : V) : Prop := ¬T.Provableₐ (⌜ℒₒᵣ⌝.neg φ)

lemma _root_.LO.FirstOrder.Theory.Consistencyₐ.quote_iff {φ : Sentence ℒₒᵣ} :
    T.Consistencyₐ (⌜φ⌝ : V) ↔ ¬T.Provableₐ (⌜∼φ⌝ : V) := by
  simp [LO.FirstOrder.Theory.Consistencyₐ, quote_sentence_eq_quote_emb (∼φ)]

section

noncomputable def _root_.LO.FirstOrder.Theory.consistencyₐ : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(ℒₒᵣ).lDef.negDef nφ φ → ¬!T.provableₐ nφ” (by simp)

lemma consistencyₐ_defined : 𝚷₁-Predicate (T.Consistencyₐ : V → Prop) via T.consistencyₐ := by
  intro v
  simp [Theory.Consistencyₐ, Theory.consistencyₐ, ((ℒₒᵣ).codeIn V).neg_defined.df.iff]

@[simp] lemma eval_consistencyₐ (v) :
    Semiformula.Evalbm V v T.consistencyₐ.val ↔ T.Consistencyₐ (v 0) := (consistencyₐ_defined T).df.iff v

instance consistencyₐ_definable : 𝚷₁-Predicate (T.Consistencyₐ : V → Prop) := (consistencyₐ_defined T).to_definable

end

end WitnessComparisons

end LO.ISigma1.Metamath
