module

public import Foundation.FirstOrder.Incompleteness.WitnessComparison
public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick

@[expose] public section
/-!
# Rosser's provability predicate
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open LO.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma rosser_quote {φ : Proposition L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simp [Theory.RosserProvable, Semiformula.quote_def]

lemma rosser_quote₀ {φ : Sentence L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simpa [Sentence.quote_def] using rosser_quote

lemma rosser_quote_def {φ : Proposition L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, Proof T b ⌜φ⌝ ∧ ∀ b' < b, ¬Proof T b' ⌜∼φ⌝ := rosser_quote

lemma rosser_quote_def₀ {φ : Sentence L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, Proof T b ⌜φ⌝ ∧ ∀ b' < b, ¬Proof T b' ⌜∼φ⌝ := by simpa [Sentence.quote_def] using! rosser_quote

theorem RosserProvable.to_provable {φ : V} : T.RosserProvable φ → Provable T φ := ProvabilityComparison.le_to_provable

lemma provable_of_standard_proof {n : ℕ} {φ : Sentence L} : Proof T (n : V) ⌜φ⌝ → T ⊢ φ := fun h ↦ by
  have : Proof T n ⌜φ⌝ ↔ Proof T (↑n : V) ⌜φ⌝ := by
    simpa [Sentence.coe_quote_eq_quote] using
      Defined.shigmaOne_absolute V (φ := proof T)
        (R := fun v ↦ Proof T (v 0) (v 1)) (R' := fun v ↦ Proof T (v 0) (v 1))
        Proof.defined Proof.defined ![n, ⌜φ⌝]
  have : Provable T (⌜φ⌝ : ℕ) := ⟨n, this.mpr h⟩
  exact provable_iff_provable.mp this

open Classical

theorem rosser_internalize [Consistent T] {φ : Sentence L} : T ⊢ φ → T.RosserProvable (⌜φ⌝ : V) := by
  intro h
  let n : ℕ := ⌜h.get⌝
  have hn : Proof T (↑n : V) ⌜φ⌝ := by simp [n, coe_quote_proof_eq]
  refine rosser_quote_def₀.mpr ⟨n, hn, ?_⟩
  intro b hb Hb
  rcases eq_nat_of_lt_nat hb with ⟨b, rfl⟩
  have : T ⊢ ∼φ := provable_of_standard_proof (V := V) Hb
  have : Inconsistent T := inconsistent_of_provable_of_unprovable h this
  have : ¬Inconsistent T := Consistent.not_inc inferInstance
  contradiction

theorem rosser_internalize_sentence [Consistent T] {σ : Sentence L} : T ⊢ σ → T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using! rosser_internalize h

open Classical in
theorem not_rosserProvable [Consistent T] {φ : Sentence L} : T ⊢ ∼φ → ¬T.RosserProvable (⌜φ⌝ : V) := by
  rintro h r
  let n : ℕ := ⌜h.get⌝
  have hn : Proof T (↑n : V) ⌜∼φ⌝ := by simp [n, coe_quote_proof_eq]
  rcases rosser_quote₀.mp r with ⟨b, hb, Hb⟩
  have : b ≤ n := by grind;
  rcases eq_nat_of_le_nat this with ⟨b, rfl⟩
  have : T ⊢ φ := provable_of_standard_proof hb
  have : Inconsistent T := inconsistent_of_provable_of_unprovable this h
  have : ¬Inconsistent T := Consistent.not_inc inferInstance
  contradiction

theorem not_rosserProvable_sentence [Consistent T] {σ : Sentence L} : T ⊢ ∼σ → ¬T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using! not_rosserProvable h

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open Bootstrapping
open LO.Entailment

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁] [Consistent T]

local prefix:90 "𝗥" => T.rosserPred

theorem rosserProvable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ 𝗥σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using rosser_internalize_sentence h

theorem rosserProvable_rosser {σ} : T ⊢ ∼σ → 𝗜𝚺₁ ⊢ ∼𝗥σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using not_rosserProvable_sentence h

end

section rosserProvability

open ProvabilityAbstraction

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁] [Consistent T]

variable (T)

noncomputable abbrev _root_.LO.FirstOrder.Theory.rosserProvability : Provability 𝗜𝚺₁ T where
  prov := T.rosserProvable
  bew_def := rosserProvable_D1

instance : T.rosserProvability.Rosser := ⟨rosserProvable_rosser⟩

lemma rosserProvability_def (σ : Sentence L) : T.rosserProvability σ = T.rosserPred σ := rfl

instance : T.rosserProvability.SoundOn ℕ := by
  constructor;
  intro σ h;
  apply Bootstrapping.provable_iff_provable.mp
    $ Bootstrapping.ProvabilityComparison.le_to_provable
    $ by simpa [models_iff, Provability.pr, Theory.RosserProvable] using h;

end rosserProvability

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete_GR (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] : Incomplete T :=
  ProvabilityAbstraction.rosser_first_incompleteness T.rosserProvability

/-- Gödel-Rosser incompleteness theorem for r.e. theories -/
theorem incomplete_GR_of_re (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T] [Consistent T] :
    Incomplete T := by
  let craig_weakerThan : 𝗜𝚺₁ ⪯ T.craig :=
    WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))
  exact (Theory.craig_equiv (T := T)).symm.incomplete
    (@incomplete_GR T.craig inferInstance craig_weakerThan inferInstance)

end LO.FirstOrder.Arithmetic
