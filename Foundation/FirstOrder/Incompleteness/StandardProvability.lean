module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D2
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D3
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import Foundation.FirstOrder.Bootstrapping.FixedPoint

@[expose] public section
/-!
# Derivability conditions of standard provability predicate
-/

namespace LO.FirstOrder.Arithmetic

open ISigma1 Bootstrapping ProvabilityAbstraction

noncomputable instance : Diagonalization 𝗜𝚺₁ where
  fixedpoint := fixedpoint
  diag θ := diagonal θ

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

/-- The derivability condition D1. -/
theorem provable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ □σ := fun h ↦
  provable_of_models _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using internalize_provability (V := V) h

/-- The derivability condition D2. -/
theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ 🡒 π) 🡒 □σ 🡒 □π :=
  provable_of_models _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T

variable (T)

noncomputable abbrev _root_.LO.FirstOrder.Theory.standardProvability : Provability 𝗜𝚺₁ T where
  prov := T.provable
  bew_def := provable_D1

variable {T}

instance : T.standardProvability.HBL2 := ⟨provable_D2⟩

lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = T.provabilityPred σ := rfl

instance [T.Δ₁] : T.standardProvability.SoundOn ℕ :=
  ⟨fun h ↦ by simpa [Arithmetic.standardProvability_def, models_iff] using h⟩

end

section arithmetic

variable {T U : ArithmeticTheory} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

lemma provable_sigma_one_complete [𝗣𝗔⁻ ⪯ T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    𝗜𝚺₁ ⊢ σ 🡒 □σ :=
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ

/-- The derivability condition D3. -/
theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : Sentence ℒₒᵣ} :
    𝗜𝚺₁ ⊢ □σ 🡒 □□σ := provable_sigma_one_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

lemma provable_D2_context [𝗜𝚺₁ ⪯ U] {Γ σ π} (hσπ : Γ ⊢[U] □(σ ➝ π)) (hσ : Γ ⊢[U] □σ) :
    Γ ⊢[U] □π := FiniteContext.of'! (weakening inferInstance provable_D2) ⨀! hσπ ⨀! hσ
🡒
lemma provable_D3_context [𝗣𝗔⁻ ⪯ T] [𝗜𝚺₁ ⪯ U] {Γ σ} (hσπ : Γ ⊢[U] □σ) :
  Γ ⊢[U] □□σ := FiniteContext.of'! (weakening inferInstance provable_D3) ⨀! hσπ

lemma provable_sound [U.SoundOnHierarchy 𝚺 1] {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦ by
  have : ℕ ⊧ₘ T.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models_iff] using this

lemma provable_complete [U.SoundOnHierarchy 𝚺 1] [𝗜𝚺₁ ⪯ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
  ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨provable_D3⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL where

instance [T.SoundOnHierarchy 𝚺 1] : T.standardProvability.Kreisel := ⟨fun h ↦ provable_sound h⟩

open LO.Entailment in
/--
  If `π` is equivalent to some 𝚺₁ sentence `σ`,
  then `π ➝ □π` is provable in `T` (note: not `𝗜𝚺₁`, compare `provable_sigma_one_complete`)
-/
lemma prov🡒ble_sigma_one_complete_of_E {σ π} [𝗜𝚺₁ ⪯ T]
  (hσ : Hierarchy 𝚺 1 σ) (hσπ : 𝗜𝚺₁ ⊢ σ 🡘 π) : 𝗜𝚺₁ ⊢ π ➝ □π := by
  apply C!_replace ?_ ?_ $ provable_sigma_one_complete (T := T) $ hσ;
  . cl_prover [hσπ];🡒
  . apply T.standardProvability.mono';
    cl_prover [hσπ];

end arithmetic

end LO.FirstOrder.Arithmetic
