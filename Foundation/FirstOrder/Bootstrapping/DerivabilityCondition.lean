import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D2
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D3
import Foundation.FirstOrder.Bootstrapping.ProvabilityAbstraction
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# Derivability conditions of standard provability predicate
-/

namespace LO.FirstOrder.Arithmetic

open ISigma1 Bootstrapping ProvabilityLogic

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
theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ ➝ π) ➝ □σ ➝ □π :=
  provable_of_models _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T

variable (T)

noncomputable abbrev _root_.LO.FirstOrder.Theory.standardProvability : Provability 𝗜𝚺₁ T where
  prov := T.provable
  D1 := provable_D1

variable {T}

instance : T.standardProvability.HBL2 := ⟨fun _ _ ↦ provable_D2⟩

lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = T.provabilityPred σ := rfl

instance [T.Δ₁] : T.standardProvability.SoundOnModel ℕ :=
  ⟨fun {σ} ↦ by simp [Arithmetic.standardProvability_def, models_iff]⟩

end

section arithmetic

variable {T : Theory ℒₒᵣ} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

lemma provable_sigma_one_complete [𝗣𝗔⁻ ⪯ T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    𝗜𝚺₁ ⊢ σ ➝ □σ :=
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ

/-- The derivability condition D3. -/
theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : Sentence ℒₒᵣ} :
    𝗜𝚺₁ ⊢ □σ ➝ □□σ := provable_sigma_one_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

variable {U : ArithmeticTheory}

lemma provable_D2_context [𝗜𝚺₁ ⪯ U] {Γ σ π} (hσπ : Γ ⊢[U] □(σ ➝ π)) (hσ : Γ ⊢[U] □σ) :
    Γ ⊢[U] □π := FiniteContext.of'! (weakening inferInstance provable_D2) ⨀! hσπ ⨀! hσ

lemma provable_D3_context [𝗣𝗔⁻ ⪯ T] [𝗜𝚺₁ ⪯ U] {Γ σ} (hσπ : Γ ⊢[U] □σ) :
  Γ ⊢[U] □□σ := FiniteContext.of'! (weakening inferInstance provable_D3) ⨀! hσπ

lemma provable_sound [U.SoundOnHierarchy 𝚺 1] {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦ by
  have : ℕ ⊧ₘ T.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models_iff] using this

lemma provable_complete [U.SoundOnHierarchy 𝚺 1] [𝗜𝚺₁ ⪯ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
  ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨fun _ ↦ provable_D3⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL where

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.GödelSound := ⟨fun h ↦ by simpa using provable_sound h⟩

instance : T.standardProvability.Sound₀ := ⟨provable_sound⟩

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.Sound := ⟨fun h ↦ provable_sound h⟩

end arithmetic

open ProvabilityLogic

end LO.FirstOrder.Arithmetic
