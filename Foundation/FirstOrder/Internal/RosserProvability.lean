import Foundation.FirstOrder.Internal.WitnessComparison

/-!
# Rosser's provability predicate
-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁Definable]

def _root_.LO.FirstOrder.Theory.RosserProvable (φ : V) : Prop := T.ProvabilityComparison φ (neg L φ)

section

def _root_.LO.FirstOrder.Theory.rosserProvable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !T.provabilityComparison φ nφ”

lemma _root_.LO.FirstOrder.Theory.RosserProvable_defined :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) via T.rosserProvable := by
  intro v
  simp [Theory.rosserProvable, Theory.RosserProvable, neg.defined.df.iff]

@[simp] lemma _root_.LO.FirstOrder.Theory.RosserProvable.eval (v) :
    Semiformula.Evalbm V v T.rosserProvable.val ↔ T.RosserProvable (v 0) := T.RosserProvable_defined.df.iff v

instance _root_.LO.FirstOrder.ArithmeticTheory.rosserProvable_definable :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) := T.RosserProvable_defined.to_definable

end

variable {T}

lemma rosser_quote {φ : SyntacticFormula L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparison (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simp [Theory.RosserProvable, Semiformula.quote_def]

def RosserProvable.to_provable {φ : V} : T.RosserProvable φ → T.Provable φ := ProvabilityComparison.to_provable

lemma provable_of_standard_proof {n : ℕ} {φ : SyntacticFormula L} : T.Proof (n : V) ⌜φ⌝ → T ⊢! φ := fun h ↦ by
  have : T.Proof n ⌜φ⌝ ↔ T.Proof (↑n : V) ⌜φ⌝ := by
    simpa [Semiformula.coe_quote_eq_quote] using
      Defined.shigmaOne_absolute V (φ := T.proof)
        (R := fun v ↦ T.Proof (v 0) (v 1)) (R' := fun v ↦ T.Proof (v 0) (v 1))
        Theory.Proof.defined Theory.Proof.defined ![n, ⌜φ⌝]
  have : T.Provable (⌜φ⌝ : ℕ) := ⟨n, this.mpr h⟩
  exact provable_iff_provable.mp this

open Classical in
def not_rosserProvable [Entailment.Consistent T] {φ : SyntacticFormula L} : T ⊢! ∼φ → ¬T.RosserProvable (⌜φ⌝ : V) := by
  rintro h r
  let n : ℕ := ⌜h.get⌝
  have hn : T.Proof (↑n : V) ⌜∼φ⌝ := by simp [n, coe_quote_proof_eq]
  rcases rosser_quote.mp r with ⟨b, hb, Hb⟩
  have : b ≤ n := by
    by_contra A
    have : ¬T.Proof (↑n : V) ⌜∼φ⌝ := Hb n (lt_of_not_ge A)
    contradiction
  rcases eq_nat_of_le_nat this with ⟨b, rfl⟩
  have : T ⊢! φ := provable_of_standard_proof hb
  have : Entailment.Inconsistent T := Entailment.inconsistent_of_provable_of_unprovable this h
  have : ¬Entailment.Inconsistent T := Entailment.Consistent.not_inc inferInstance
  contradiction

end LO.ISigma1.Metamath
