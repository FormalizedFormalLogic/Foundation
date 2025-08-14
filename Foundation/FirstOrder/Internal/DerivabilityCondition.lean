import Foundation.FirstOrder.Internal.DerivabilityCondition.D1
import Foundation.FirstOrder.Internal.DerivabilityCondition.D2
import Foundation.FirstOrder.Internal.DerivabilityCondition.D3
import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Derivability conditions of standard provability predicate

-/

namespace LO.FirstOrder.Arithmetic

open ISigma1 Metamath ProvabilityLogic

instance : Diagonalization 𝐈𝚺₁ where
  fixpoint := fixpoint
  diag θ := diagonal θ

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

theorem provable_D1 {σ} : T ⊢!. σ → 𝐈𝚺₁ ⊢!. □σ := fun h ↦
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using provable_of_provable_arith₀ (V := V) h

theorem provable_D2 {σ π} : 𝐈𝚺₁ ⊢!. □(σ ➝ π) ➝ □σ ➝ □π :=
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using modus_ponens_sentence T

variable (T)

abbrev _root_.LO.FirstOrder.Theory.standardProvability : Provability 𝐈𝚺₁ T where
  prov := T.provable
  D1 := provable_D1

variable {T}

instance : T.standardProvability.HBL2 := ⟨fun _ _ ↦ provable_D2⟩

lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = T.provabilityPred σ := rfl

instance [T.Δ₁] : T.standardProvability.SoundOnModel ℕ :=
  ⟨fun {σ} ↦ by simp [Arithmetic.standardProvability_def, models₀_iff]⟩

end

section arithmetic

variable {T : Theory ℒₒᵣ} [T.Δ₁]

local prefix:90 "□" => T.provabilityPred

lemma provable_sigma_one_complete [𝐏𝐀⁻ ⪯ T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    𝐈𝚺₁ ⊢!. σ ➝ □σ :=
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using InternalArithmetic.sigma_one_complete (T := T) (V := V) hσ

theorem provable_D3 [𝐏𝐀⁻ ⪯ T] {σ : Sentence ℒₒᵣ} :
    𝐈𝚺₁ ⊢!. □σ ➝ □□σ := provable_sigma_one_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

variable {U : ArithmeticTheory} [U.SoundOnHierarchy 𝚺 1]

lemma provable_sound {σ} : U ⊢!. □σ → T ⊢!. σ := fun h ↦ by
  have : ℕ ⊧ₘ₀ T.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models₀_iff] using this

lemma provable_complete [𝐈𝚺₁ ⪯ U] {σ} : T ⊢!. σ ↔ U ⊢!. □σ :=
  ⟨fun h ↦ Entailment.weakening inferInstance (provable_D1 h), provable_sound⟩

instance [𝐏𝐀⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨fun _ ↦ provable_D3⟩

instance [𝐏𝐀⁻ ⪯ T] : T.standardProvability.HBL where

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.GoedelSound := ⟨fun h ↦ by simpa using provable_sound h⟩

instance : T.standardProvability.Sound₀ := ⟨provable_sound⟩

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.standardProvability.Sound := ⟨fun h ↦ provable_sound h⟩

end arithmetic

open ProvabilityLogic

end LO.FirstOrder.Arithmetic
