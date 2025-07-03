import Foundation.FirstOrder.Incompleteness.StandardProvability.D1
import Foundation.FirstOrder.Incompleteness.StandardProvability.D3
import Foundation.FirstOrder.Incompleteness.DerivabilityCondition.Basic
import Foundation.FirstOrder.Incompleteness.FixedPoint

/-!
# Derivability conditions of standard provability predicate

-/

namespace LO.ISigma1

open FirstOrder Arith PeanoMinus IOpen ISigma0 Metamath Arithmetization

variable {T : Theory ℒₒᵣ} [𝐈𝚺₁ ⪯ T]

section

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

noncomputable abbrev _root_.LO.FirstOrder.Theory.bewₐ (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := U.provableₐ/[⌜σ⌝]

noncomputable abbrev _root_.LO.FirstOrder.Theory.consistentₐ : Sentence ℒₒᵣ := ∼U.bewₐ ⊥

abbrev _root_.LO.FirstOrder.Theory.Consistentₐ : Theory ℒₒᵣ := {↑U.consistentₐ}

notation "𝐂𝐨𝐧[" U "]" => LO.FirstOrder.Theory.Consistentₐ U

abbrev _root_.LO.FirstOrder.Theory.Inconsistentₐ : Theory ℒₒᵣ := {∼↑U.consistentₐ}

notation "¬𝐂𝐨𝐧[" U "]" => LO.FirstOrder.Theory.Inconsistentₐ U

noncomputable def _root_.LO.FirstOrder.Theory.goedelₐ : Sentence ℒₒᵣ := fixpoint (∼U.provableₐ)

end

section

variable {U : Theory ℒₒᵣ} [U.Delta1Definable]

theorem provableₐ_D1 {σ} : U ⊢!. σ → T ⊢!. U.bewₐ σ := by
  intro h
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  apply complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using provableₐ_of_provable (T := U) (V := V) h

theorem provableₐ_D2 {σ π} : T ⊢!. U.bewₐ (σ ➝ π) ➝ U.bewₐ σ ➝ U.bewₐ π :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using modus_ponens₀

lemma provableₐ_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    T ⊢!. σ ➝ U.bewₐ σ :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using sigma₁_complete (T := U) (V := V) hσ

theorem provableₐ_D3 {σ : Sentence ℒₒᵣ} :
    T ⊢!. U.bewₐ σ ➝ U.bewₐ (U.bewₐ σ) := provableₐ_sigma₁_complete (by simp)

lemma goedel_iff_unprovable_goedel : T ⊢!. U.goedelₐ ⭤ ∼U.bewₐ U.goedelₐ := by
  simpa [Theory.goedelₐ, Theory.bewₐ] using diagonal (∼U.provableₐ)

open LO.Entailment LO.Entailment.FiniteContext

lemma provableₐ_D2_context {Γ σ π} (hσπ : Γ ⊢[T.alt]! (U.bewₐ (σ ➝ π))) (hσ : Γ ⊢[T.alt]! U.bewₐ σ) :
    Γ ⊢[T.alt]! U.bewₐ π := of'! provableₐ_D2 ⨀ hσπ ⨀ hσ

lemma provableₐ_D3_context {Γ σ} (hσπ : Γ ⊢[T.alt]! U.bewₐ σ) : Γ ⊢[T.alt]! U.bewₐ (U.bewₐ σ) := of'! provableₐ_D3 ⨀ hσπ

variable [ℕ ⊧ₘ* T] [𝐑₀ ⪯ U]

omit [𝐈𝚺₁ ⪯ T] in
lemma provableₐ_sound {σ} : T ⊢!. U.bewₐ σ → U ⊢! ↑σ := by
  intro h
  have : U.Provableₐ (⌜σ⌝ : ℕ) := by simpa [models₀_iff] using consequence_iff.mp (sound! (T := T) h) ℕ inferInstance
  simpa using this

lemma provableₐ_complete {σ} : U ⊢! ↑σ ↔ T ⊢!. U.bewₐ σ := ⟨provableₐ_D1, provableₐ_sound⟩

end

end LO.ISigma1

namespace LO.FirstOrder.Arith

open DerivabilityCondition

open PeanoMinus IOpen ISigma0 ISigma1 Metamath Arithmetization

variable (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T]

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

noncomputable instance : Diagonalization T where
  fixpoint := fixpoint
  diag θ := diagonal θ

/-- TODO: rename to `standardPP`-/
noncomputable abbrev _root_.LO.FirstOrder.Theory.standardDP : ProvabilityPredicate T U where
  prov := U.provableₐ
  D1 := provableₐ_D1

instance : (Theory.standardDP T U).HBL2 := ⟨provableₐ_D2⟩
instance : (Theory.standardDP T U).HBL3 := ⟨provableₐ_D3⟩
instance : (Theory.standardDP T U).HBL := ⟨⟩
instance [ℕ ⊧ₘ* U] [𝐑₀ ⪯ U] : (Theory.standardDP T U).GoedelSound := ⟨fun h ↦ by simpa using provableₐ_sound h⟩

lemma standardDP_def (σ : Sentence ℒₒᵣ) : (T.standardDP U) σ = U.provableₐ.val/[⌜σ⌝] := rfl

end LO.FirstOrder.Arith
