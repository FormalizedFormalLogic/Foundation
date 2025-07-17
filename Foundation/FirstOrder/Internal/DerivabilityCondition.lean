import Foundation.FirstOrder.Internal.D1
import Foundation.FirstOrder.Internal.D2
import Foundation.FirstOrder.Internal.D3
import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Derivability conditions of standard provability predicate

-/

namespace LO.ISigma1

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 Metamath InternalArithmetic

variable {T : ArithmeticTheory} [𝐈𝚺₁ ⪯ T] {U : ArithmeticTheory} [U.Δ₁Definable]

local prefix:90 "□" => U.provabilityPred

theorem provable_D1 {σ} : U ⊢!. σ → T ⊢!. □σ := by
  intro h
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  apply complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using provable_of_provable_arith₀ (T := U) (V := V) h

theorem provable_D2 {σ π} : T ⊢!. □(σ ➝ π) ➝ □σ ➝ □π :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using modus_ponens_sentence U

lemma provable_sigma_one_complete [𝐏𝐀⁻ ⪯ U] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    T ⊢!. σ ➝ □σ :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using sigma_one_complete (T := U) (V := V) hσ

theorem provable_D3 [𝐏𝐀⁻ ⪯ U] {σ : Sentence ℒₒᵣ} :
    T ⊢!. □σ ➝ □□σ := provable_sigma_one_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

lemma provable_D2_context {Γ σ π} (hσπ : Γ ⊢[T.toAxiom]! (□(σ ➝ π))) (hσ : Γ ⊢[T.toAxiom]! □σ) :
    Γ ⊢[T.toAxiom]! □π := of'! provable_D2 ⨀ hσπ ⨀ hσ

lemma provable_D3_context [𝐏𝐀⁻ ⪯ U] {Γ σ} (hσπ : Γ ⊢[T.toAxiom]! □σ) : Γ ⊢[T.toAxiom]! □(□σ) := of'! provable_D3 ⨀ hσπ

variable [T.SoundOnHierarchy 𝚺 1]

omit [𝐈𝚺₁ ⪯ T] in
lemma provable_sound {σ} : T ⊢!. □σ → U ⊢!. σ := by
  intro h
  have : ℕ ⊧ₘ₀ U.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models₀_iff] using this

lemma provable_complete {σ} : U ⊢!. σ ↔ T ⊢!. □σ := ⟨provable_D1, provable_sound⟩

end LO.ISigma1

namespace LO.FirstOrder.Arithmetic

open ProvabilityLogic

open PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

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
