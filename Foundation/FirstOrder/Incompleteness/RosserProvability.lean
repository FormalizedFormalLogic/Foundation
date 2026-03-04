module

public import Foundation.FirstOrder.Incompleteness.WitnessComparison

@[expose] public section
/-!
# Rosser's provability predicate
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

def _root_.LO.FirstOrder.Theory.RosserProvable (φ : V) : Prop := T.ProvabilityComparisonLE φ (neg L φ)

section

noncomputable def _root_.LO.FirstOrder.Theory.rosserProvable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !T.provabilityComparisonLE φ nφ”

instance _root_.LO.FirstOrder.Theory.RosserProvable_defined :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) via T.rosserProvable := .mk fun v ↦ by
  simp [Theory.rosserProvable, Theory.RosserProvable]

instance _root_.LO.FirstOrder.Theory.rosserProvable_definable :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) := T.RosserProvable_defined.to_definable

noncomputable abbrev _root_.LO.FirstOrder.Theory.rosserPred (σ : Sentence L) : ArithmeticSentence := T.rosserProvable.val/[⌜σ⌝]

end

variable {T}

lemma rosser_quote {φ : SyntacticFormula L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simp [Theory.RosserProvable, Semiformula.quote_def]

lemma rosser_quote₀ {φ : Sentence L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simpa [Sentence.quote_def] using rosser_quote

lemma rosser_quote_def {φ : SyntacticFormula L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, T.Proof b ⌜φ⌝ ∧ ∀ b' < b, ¬T.Proof b' ⌜∼φ⌝ := rosser_quote

lemma rosser_quote_def₀ {φ : Sentence L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, T.Proof b ⌜φ⌝ ∧ ∀ b' < b, ¬T.Proof b' ⌜∼φ⌝ := by simpa [Sentence.quote_def] using rosser_quote

def RosserProvable.to_provable {φ : V} : T.RosserProvable φ → T.Provable φ := ProvabilityComparison.le_to_provable

lemma provable_of_standard_proof {n : ℕ} {φ : Sentence L} : T.Proof (n : V) ⌜φ⌝ → T ⊢ φ := fun h ↦ by
  have : T.Proof n ⌜φ⌝ ↔ T.Proof (↑n : V) ⌜φ⌝ := by
    simpa [Sentence.coe_quote_eq_quote] using
      Defined.shigmaOne_absolute V (φ := T.proof)
        (R := fun v ↦ T.Proof (v 0) (v 1)) (R' := fun v ↦ T.Proof (v 0) (v 1))
        Theory.Proof.defined Theory.Proof.defined ![n, ⌜φ⌝]
  have : T.Provable (⌜φ⌝ : ℕ) := ⟨n, this.mpr h⟩
  exact provable_iff_provable.mp this

open Classical

def rosser_internalize [Entailment.Consistent T] {φ : Sentence L} : T ⊢ φ → T.RosserProvable (⌜φ⌝ : V) := by
  intro h
  let n : ℕ := ⌜h.get⌝
  have hn : T.Proof (↑n : V) ⌜φ⌝ := by simp [n, coe_quote_proof_eq]
  refine rosser_quote_def₀.mpr ⟨n, hn, ?_⟩
  intro b hb Hb
  rcases eq_nat_of_lt_nat hb with ⟨b, rfl⟩
  have : T ⊢ ∼φ := provable_of_standard_proof (V := V) Hb
  have : Entailment.Inconsistent T := Entailment.inconsistent_of_provable_of_unprovable h this
  have : ¬Entailment.Inconsistent T := Entailment.Consistent.not_inc inferInstance
  contradiction

def rosser_internalize_sentence [Entailment.Consistent T] {σ : Sentence L} : T ⊢ σ → T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using rosser_internalize h

open Classical in
def not_rosserProvable [Entailment.Consistent T] {φ : Sentence L} : T ⊢ ∼φ → ¬T.RosserProvable (⌜φ⌝ : V) := by
  rintro h r
  let n : ℕ := ⌜h.get⌝
  have hn : T.Proof (↑n : V) ⌜∼φ⌝ := by simp [n, coe_quote_proof_eq]
  rcases rosser_quote₀.mp r with ⟨b, hb, Hb⟩
  have : b ≤ n := by grind;
  rcases eq_nat_of_le_nat this with ⟨b, rfl⟩
  have : T ⊢ φ := provable_of_standard_proof hb
  have : Entailment.Inconsistent T := Entailment.inconsistent_of_provable_of_unprovable this h
  have : ¬Entailment.Inconsistent T := Entailment.Consistent.not_inc inferInstance
  contradiction

def not_rosserProvable_sentence [Entailment.Consistent T] {σ : Sentence L} : T ⊢ ∼σ → ¬T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using not_rosserProvable h

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁] [Entailment.Consistent T]

local prefix:90 "𝗥" => T.rosserPred

theorem rosserProvable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ 𝗥σ := fun h ↦
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using rosser_internalize_sentence h

theorem rosserProvable_rosser {σ} : T ⊢ ∼σ → 𝗜𝚺₁ ⊢ ∼𝗥σ := fun h ↦
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using not_rosserProvable_sentence h

end

open ProvabilityAbstraction

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁] [Entailment.Consistent T]

variable (T)

noncomputable abbrev _root_.LO.FirstOrder.Theory.rosserProvability : Provability 𝗜𝚺₁ T where
  prov := T.rosserProvable
  bew_def := rosserProvable_D1

instance : T.rosserProvability.Rosser := ⟨rosserProvable_rosser⟩

lemma rosserProvability_def (σ : Sentence L) : T.rosserProvability σ = T.rosserPred σ := rfl

instance [T.Δ₁] : T.rosserProvability.SoundOn ℕ := by
  constructor;
  intro σ h;
  apply Bootstrapping.provable_iff_provable.mp
    $ Bootstrapping.ProvabilityComparison.le_to_provable
    $ by simpa [models_iff, Provability.pr, Theory.RosserProvable] using h;

end LO.FirstOrder.Arithmetic
