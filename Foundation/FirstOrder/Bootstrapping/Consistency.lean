import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition

/-!
# Consistency predicate
-/

open Classical

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

section

variable (T : Theory L) [T.Δ₁] (V)

def _root_.LO.FirstOrder.Theory.Consistent : Prop := ¬T.Provable (⌜(⊥ : Sentence L)⌝ : V)

variable {V}

def _root_.LO.FirstOrder.Theory.ConsistentWith (φ : V) : Prop := ¬T.Provable (neg L φ)

lemma _root_.LO.FirstOrder.Theory.ConsistentWith.quote_iff {σ : Sentence L} :
    T.ConsistentWith (⌜σ⌝ : V) ↔ ¬T.Provable (⌜∼σ⌝ : V) := by
  simp [Theory.ConsistentWith, Sentence.quote_def, Semiformula.quote_def]

section

noncomputable def _root_.LO.FirstOrder.Theory.consistent : 𝚷₁.Sentence :=
  .mkPi (∼T.provabilityPred ⊥)

@[simp] lemma consistent.defined : Semiformula.Evalbm V ![] (T.consistent : Sentence ℒₒᵣ) ↔ T.Consistent V := by
  simp [Theory.consistent, Theory.Consistent]

noncomputable def _root_.LO.FirstOrder.Theory.consistentWith : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(negGraph L) nφ φ → ¬!T.provable nφ”

instance consistentWith.defined : 𝚷₁-Predicate (T.ConsistentWith : V → Prop) via T.consistentWith := .mk fun v ↦ by
  simp [Theory.ConsistentWith, Theory.consistentWith]

instance consistentWith.definable : 𝚷₁-Predicate (T.ConsistentWith : V → Prop) := (consistentWith.defined T).to_definable

noncomputable abbrev _root_.LO.FirstOrder.Theory.consistentWithPred (σ : Sentence L) : Sentence ℒₒᵣ := T.consistentWith.val/[⌜σ⌝]

noncomputable def _root_.LO.FirstOrder.Theory.consistentWithPred' (σ : Sentence L) : 𝚷₁.Sentence := .mkPi
  “!T.consistentWith !!(⌜σ⌝)”

@[simp] lemma consistentWithPred'_val (σ : Sentence L) : (T.consistentWithPred' σ).val = T.consistentWithPred' σ := by rfl

variable {T}

end

abbrev _root_.LO.FirstOrder.Theory.Con : ArithmeticTheory := {↑T.consistent}

abbrev _root_.LO.FirstOrder.Theory.Incon : ArithmeticTheory := {∼↑T.consistent}

noncomputable instance : T.Con.Δ₁ := Theory.Δ₁.singleton _

noncomputable instance : T.Incon.Δ₁ := Theory.Δ₁.singleton _

end

variable (T : ArithmeticTheory) [T.Δ₁] (V)

def consistent_eq : T.consistent = T.standardProvability.con := rfl

@[simp] lemma standard_consistent [𝗥₀ ⪯ T] : T.Consistent ℕ ↔ Entailment.Consistent T := by
  simp [Theory.Consistent, Entailment.consistent_iff_unprovable_bot]

end WitnessComparisons

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Entailment

variable (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] [T.Δ₁]

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + T.Con := by
  have : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (inferInstanceAs (𝗥₀ ⪯ 𝗜𝚺₁)) inferInstance
  have : Entailment.Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]

end LO.FirstOrder.Arithmetic
