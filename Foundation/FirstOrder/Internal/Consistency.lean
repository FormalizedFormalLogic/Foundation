import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Consistency predicate
-/

open Classical

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

section

variable (T : Theory L) [T.Δ₁Definable] (V)

def _root_.LO.FirstOrder.Theory.IsConsistent : Prop := ¬T.Provable (⌜(⊥ : Sentence L)⌝ : V)

variable {V}

def _root_.LO.FirstOrder.Theory.Consistency (φ : V) : Prop := ¬T.Provable (neg L φ)

lemma _root_.LO.FirstOrder.Theory.Consistency.quote_iff {σ : Sentence L} :
    T.Consistency (⌜σ⌝ : V) ↔ ¬T.Provable (⌜∼σ⌝ : V) := by
  simp [Theory.Consistency, Semiformula.empty_quote_def, Semiformula.quote_def]

section

def _root_.LO.FirstOrder.Theory.isConsistent : 𝚷₁.Sentence :=
  .mkPi (∼T.provabilityPred ⊥)

@[simp] lemma isConsistent.defined : Semiformula.Evalbm V ![] (T.isConsistent : Sentence ℒₒᵣ) ↔ T.IsConsistent V := by
  simp [Theory.isConsistent, Theory.IsConsistent]

def _root_.LO.FirstOrder.Theory.consistency : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(negGraph L) nφ φ → ¬!T.provable nφ”

lemma consistency.defined : 𝚷₁-Predicate (T.Consistency : V → Prop) via T.consistency := by
  intro v
  simp [Theory.Consistency, Theory.consistency, neg.defined.df.iff]

@[simp] lemma consistency.eval (v) :
    Semiformula.Evalbm V v T.consistency.val ↔ T.Consistency (v 0) := (consistency.defined T).df.iff v

instance consistency.definable : 𝚷₁-Predicate (T.Consistency : V → Prop) := (consistency.defined T).to_definable

end

abbrev _root_.LO.FirstOrder.Theory.Con : ArithmeticTheory := {↑T.isConsistent}

abbrev _root_.LO.FirstOrder.Theory.Incon : ArithmeticTheory := {∼↑T.isConsistent}

instance : T.Con.Δ₁Definable := Theory.Δ₁Definable.singleton _

instance : T.Incon.Δ₁Definable := Theory.Δ₁Definable.singleton _

end

variable (T : ArithmeticTheory) [T.Δ₁Definable] (V)

def isConsistent_eq : T.isConsistent = T.standardPr.con := rfl

@[simp] lemma standard_isConsistent [𝐑₀ ⪯ T] : T.IsConsistent ℕ ↔ Entailment.Consistent T := by
  simp [Theory.IsConsistent, Entailment.consistent_iff_unprovable_bot, Axiom.provable_iff]

end WitnessComparisons

end LO.ISigma1.Metamath

namespace LO.FirstOrder.Arithmetic

open Entailment ProvabilityLogic

variable (T : ArithmeticTheory) [𝐈𝚺₁ ⪯ T] [T.Δ₁Definable]

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + T.Con := by
  have : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  have : Entailment.Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]

end LO.FirstOrder.Arithmetic
