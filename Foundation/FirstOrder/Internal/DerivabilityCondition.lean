import Foundation.FirstOrder.Internal.D1
import Foundation.FirstOrder.Internal.D2
import Foundation.FirstOrder.Internal.D3
import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Derivability conditions of standard provability predicate

-/

namespace LO.FirstOrder.Arithmetic

open ISigma1 Metamath

section

variable {T : ArithmeticTheory} [T.Δ₁Definable]

local prefix:90 "□" => T.provabilityPred

theorem provable_D1 {σ} : T ⊢!. σ → 𝐈𝚺₁ ⊢!. □σ := fun h ↦
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using provable_of_provable_arith₀ (V := V) h

theorem provable_D2 {σ π} : 𝐈𝚺₁ ⊢!. □(σ ➝ π) ➝ □σ ➝ □π :=
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using modus_ponens_sentence T

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

end

open ProvabilityLogic

variable (T : ArithmeticTheory) [T.Δ₁Definable]

instance : Diagonalization 𝐈𝚺₁ where
  fixpoint := fixpoint
  diag θ := diagonal θ

abbrev _root_.LO.FirstOrder.ArithmeticTheory.standardPr : ProvabilityPredicate 𝐈𝚺₁ T where
  prov := T.provable
  D1 := provable_D1

instance : T.standardPr.HBL2 := ⟨fun _ _ ↦ provable_D2⟩

instance [𝐏𝐀⁻ ⪯ T] : T.standardPr.HBL3 := ⟨fun _ ↦ provable_D3⟩

instance [𝐏𝐀⁻ ⪯ T] : T.standardPr.HBL where

instance [T.SoundOnHierarchy 𝚺 1] : T.standardPr.GoedelSound := ⟨fun h ↦ by simpa using provable_sound h⟩

lemma standardPr_def (σ : Sentence ℒₒᵣ) : T.standardPr σ = T.provabilityPred σ := rfl

instance [T.Δ₁Definable] : T.standardPr.Sound ℕ := ⟨fun {σ} ↦ by simp [Arithmetic.standardPr_def, models₀_iff]⟩

end LO.FirstOrder.Arithmetic
