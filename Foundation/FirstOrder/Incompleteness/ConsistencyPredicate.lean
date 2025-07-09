import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Consistency predicate

-/

open Classical

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable (T : ArithmeticTheory) [T.Delta1Definable] (V)

def _root_.LO.FirstOrder.ArithmeticTheory.IsConsistent : Prop := ¬T.Provable (⌜(⊥ : ArithmeticSentence)⌝ : V)

variable {V}

def _root_.LO.FirstOrder.ArithmeticTheory.Consistency (φ : V) : Prop := ¬T.Provable (neg ℒₒᵣ φ)

lemma _root_.LO.FirstOrder.Theory.Consistency.quote_iff {φ : Sentence ℒₒᵣ} :
    T.Consistency (⌜φ⌝ : V) ↔ ¬T.Provable (⌜∼φ⌝ : V) := by
  simp [ArithmeticTheory.Consistency, quote_sentence_eq_quote_emb (∼φ)]

section

def _root_.LO.FirstOrder.ArithmeticTheory.isConsistent : 𝚷₁.Sentence :=
  .mkPi (∼T.provabilityPred ⊥)

@[simp] lemma isConsistent_defined : Semiformula.Evalbm V ![] (T.isConsistent : Sentence ℒₒᵣ) ↔ T.IsConsistent V := by
  simp [ArithmeticTheory.isConsistent, ArithmeticTheory.IsConsistent]

def _root_.LO.FirstOrder.ArithmeticTheory.consistency : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(ℒₒᵣ).lDef.negDef nφ φ → ¬!T.provable nφ”

lemma consistency_defined : 𝚷₁-Predicate (T.Consistency : V → Prop) via T.consistency := by
  intro v
  simp [ArithmeticTheory.Consistency, ArithmeticTheory.consistency, ((ℒₒᵣ).codeIn V).neg_defined.df.iff]

@[simp] lemma eval_consistency (v) :
    Semiformula.Evalbm V v T.consistency.val ↔ T.Consistency (v 0) := (consistency_defined T).df.iff v

instance consistency_definable : 𝚷₁-Predicate (T.Consistency : V → Prop) := (consistency_defined T).to_definable

end

def isConsistent_eq : T.isConsistent = T.standardPr.con := rfl

@[simp] lemma standard_isConsistent [𝐑₀ ⪯ T] : T.IsConsistent ℕ ↔ Entailment.Consistent T := by
  simp [ArithmeticTheory.IsConsistent, Entailment.consistent_iff_unprovable_bot, Axiom.provable_iff]

end WitnessComparisons



end LO.ISigma1.Metamath

namespace LO.FirstOrder.Arithmetic

open Entailment ProvabilityLogic

variable (T : ArithmeticTheory) [𝐈𝚺₁ ⪯ T] [T.Delta1Definable]

abbrev _root_.LO.FirstOrder.ArithmeticTheory.Con : ArithmeticTheory := {↑T.isConsistent}

abbrev _root_.LO.FirstOrder.ArithmeticTheory.Incon : ArithmeticTheory := {∼↑T.isConsistent}

instance : T.Con.Delta1Definable := Theory.Delta1Definable.singleton _

instance : T.Incon.Delta1Definable := Theory.Delta1Definable.singleton _

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + T.Con := by
  have : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  have : Entailment.Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]

end LO.FirstOrder.Arithmetic
