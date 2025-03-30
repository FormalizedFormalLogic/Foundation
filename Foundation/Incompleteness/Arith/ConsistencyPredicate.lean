import Foundation.Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

noncomputable section

open Classical
namespace LO.Arith

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

def _root_.LO.FirstOrder.Theory.Consistencyₐ (φ : V) : Prop := ¬T.Provableₐ (⌜ℒₒᵣ⌝.neg φ)

lemma _root_.LO.FirstOrder.Theory.Consistencyₐ.quote {φ : Sentence ℒₒᵣ} :
    T.Consistencyₐ (⌜φ⌝ : V) ↔ ¬T.Provableₐ (⌜∼φ⌝ : V) := by
  simp [LO.FirstOrder.Theory.Consistencyₐ, quote_sentence_eq_quote_emb (∼φ)]

section

def _root_.LO.FirstOrder.Theory.consistencyₐDef : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(ℒₒᵣ).lDef.negDef nφ φ → ¬!T.provableₐ nφ” (by simp)

lemma consistencyₐ_defined : 𝚷₁-Predicate (T.Consistencyₐ : V → Prop) via T.consistencyₐDef := by
  intro v
  simp [Theory.Consistencyₐ, Theory.consistencyₐDef, ((ℒₒᵣ).codeIn V).neg_defined.df.iff]

@[simp] lemma eval_consistencyₐDef (v) :
    Semiformula.Evalbm V v T.consistencyₐDef.val ↔ T.Consistencyₐ (v 0) := (consistencyₐ_defined T).df.iff v

instance consistencyₐ_definable : 𝚷₁-Predicate (T.Consistencyₐ : V → Prop) := (consistencyₐ_defined T).to_definable

end

variable {T}
