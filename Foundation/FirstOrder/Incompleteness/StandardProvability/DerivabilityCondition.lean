import Foundation.FirstOrder.Incompleteness.StandardProvability.D1
import Foundation.FirstOrder.Incompleteness.StandardProvability.D3
import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Incompleteness.FixedPoint

/-!
# Derivability conditions of standard provability predicate

-/

namespace LO.ISigma1

open FirstOrder Arith PeanoMinus IOpen ISigma0 Metamath Arithmetization

variable {T : ArithmeticTheory} [𝐈𝚺₁ ⪯ T]

section

variable (U : ArithmeticTheory) [U.Delta1Definable]

noncomputable abbrev _root_.LO.FirstOrder.ArithmeticTheory.provabilityPred (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := U.provable/[⌜σ⌝]

/-
noncomputable abbrev _root_.LO.FirstOrder.ArithmeticTheory.consistent : Sentence ℒₒᵣ := ∼U.provabilityPred ⊥

abbrev _root_.LO.FirstOrder.ArithmeticTheory.Consistent : ArithmeticTheory := {↑U.consistent}

abbrev _root_.LO.FirstOrder.ArithmeticTheory.Inconsistent : ArithmeticTheory := {∼↑U.consistent}
-/

end

section

variable {U : ArithmeticTheory} [U.Delta1Definable]

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
    simpa [models_iff] using modus_ponens₀

lemma provable_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    T ⊢!. σ ➝ □σ :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using sigma₁_complete (T := U) (V := V) hσ

theorem provable_D3 {σ : Sentence ℒₒᵣ} :
    T ⊢!. □σ ➝ □□σ := provable_sigma₁_complete (by simp)

open LO.Entailment LO.Entailment.FiniteContext

lemma provable_D2_context {Γ σ π} (hσπ : Γ ⊢[T.toAxiom]! (□(σ ➝ π))) (hσ : Γ ⊢[T.toAxiom]! □σ) :
    Γ ⊢[T.toAxiom]! □π := of'! provable_D2 ⨀ hσπ ⨀ hσ

lemma provable_D3_context {Γ σ} (hσπ : Γ ⊢[T.toAxiom]! □σ) : Γ ⊢[T.toAxiom]! □(□σ) := of'! provable_D3 ⨀ hσπ

variable [T.Sigma1Sound] [𝐑₀ ⪯ U]

omit [𝐈𝚺₁ ⪯ T] in
lemma provable_sound {σ} : T ⊢!. □σ → U ⊢!. σ := by
  intro h
  have : ℕ ⊧ₘ₀ U.provabilityPred σ := ArithmeticTheory.SoundOn.sound (F := Arith.Hierarchy 𝚺 1) h (by simp)
  simpa [models₀_iff] using this

lemma provable_complete {σ} : U ⊢!. σ ↔ T ⊢!. □σ := ⟨provable_D1, provable_sound⟩

end

end LO.ISigma1

namespace LO.FirstOrder.Arith

open ProvabilityLogic

open PeanoMinus IOpen ISigma0 ISigma1 Metamath Arithmetization

variable (T : ArithmeticTheory) [T.Delta1Definable]

noncomputable instance : Diagonalization 𝐈𝚺₁ where
  fixpoint := fixpoint
  diag θ := diagonal θ

noncomputable abbrev _root_.LO.FirstOrder.Theory.standardPr : ProvabilityPredicate 𝐈𝚺₁ T where
  prov := T.provable
  D1 := provable_D1

instance : T.standardPr.HBL2 := ⟨fun _ _ ↦ provable_D2⟩

instance : T.standardPr.HBL3 := ⟨fun _ ↦ provable_D3⟩

instance : T.standardPr.HBL where

instance [T.Sigma1Sound] [𝐑₀ ⪯ T] : T.standardPr.GoedelSound := ⟨fun h ↦ by simpa using provable_sound h⟩

lemma standardPr_def (σ : Sentence ℒₒᵣ) : T.standardPr σ = T.provabilityPred σ := rfl

instance [𝐑₀ ⪯ T] [T.Delta1Definable] : T.standardPr.Sound ℕ := ⟨fun {σ} ↦ by simp [Arith.standardPr_def, models₀_iff]⟩

end LO.FirstOrder.Arith
