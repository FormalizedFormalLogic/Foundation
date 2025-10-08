import Foundation.FirstOrder.Internal.DerivabilityCondition.D1
import Foundation.FirstOrder.Internal.DerivabilityCondition.D2
import Foundation.FirstOrder.Internal.DerivabilityCondition.D3
import Foundation.ProvabilityLogic.Provability
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Derivability conditions of standard provability predicate
-/

namespace LO.FirstOrder.Arithmetic

open ISigma1 Metamath ProvabilityLogic

noncomputable instance : Diagonalization 𝗜𝚺₁ where
  fixedpoint := fixedpoint
  diag θ := diagonal θ

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

theorem provable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ □σ := fun h ↦
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using internalize_provability (V := V) h

theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ ➝ π) ➝ □σ ➝ □π :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using modus_ponens_sentence T

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
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using InternalArithmetic.sigma_one_complete (T := T) (V := V) hσ

theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : Sentence ℒₒᵣ} :
    𝗜𝚺₁ ⊢ □σ ➝ □□σ := provable_sigma_one_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

variable {U : ArithmeticTheory} [U.SoundOnHierarchy 𝚺 1]

lemma provable_sound {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦ by
  have : ℕ ⊧ₘ T.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models_iff] using this

lemma provable_complete [𝗜𝚺₁ ⪯ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
  ⟨fun h ↦ Entailment.weakening inferInstance (provable_D1 h), provable_sound⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨fun _ ↦ provable_D3⟩

instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL where

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.GödelSound := ⟨fun h ↦ by simpa using provable_sound h⟩

instance : T.standardProvability.Sound₀ := ⟨provable_sound⟩

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.Sound := ⟨fun h ↦ provable_sound h⟩

end arithmetic

open ProvabilityLogic

end LO.FirstOrder.Arithmetic
