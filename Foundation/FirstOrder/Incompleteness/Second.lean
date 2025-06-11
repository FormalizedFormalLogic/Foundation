import Foundation.FirstOrder.Incompleteness.FixedPoint

/-!
# Gödel's second incompleteness theorem over $\mathsf{I}\Sigma_1$

-/

open Classical

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

section

variable (T)

variable [T.Delta1Definable]

open LO.Entailment LO.Entailment.FiniteContext

local notation "𝗚" => T.goedelₐ

local notation "𝗖𝗼𝗻" => T.consistentₐ

local prefix:max "□" => T.bewₐ

lemma goedel_unprovable [Entailment.Consistent T] : T ⊬ ↑𝗚 := by
  intro h
  have hp : T ⊢! ↑□𝗚 := provableₐ_D1 h
  have hn : T ⊢! ∼↑□𝗚 := by simpa [provable₀_iff] using K!_left goedel_iff_unprovable_goedel ⨀ h
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable hp hn) inferInstance

lemma not_goedel_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑𝗚 := fun h ↦ by
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  have : T ⊢!. □𝗚 := Entailment.CN!_of_CN!_left (K!_right goedel_iff_unprovable_goedel) ⨀ (by simpa [provable₀_iff] using h)
  have : T ⊢! ↑𝗚 := provableₐ_sound this
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h)
    (Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩)

lemma consistent_iff_goedel : T ⊢! ↑𝗖𝗼𝗻 ⭤ ↑𝗚 := by
  apply E!_intro
  · have bew_G : [∼𝗚] ⊢[T.alt]! □𝗚 := deductInv'! <| CN!_of_CN!_left <| K!_right goedel_iff_unprovable_goedel
    have bew_not_bew_G : [∼𝗚] ⊢[T.alt]! □(∼□𝗚) := by
      have : T ⊢!. □(𝗚 ➝ ∼□𝗚) := provableₐ_D1 <| K!_left goedel_iff_unprovable_goedel
      exact provableₐ_D2_context (of'! this) bew_G
    have bew_bew_G : [∼𝗚] ⊢[T.alt]! □□𝗚 := provableₐ_D3_context bew_G
    have : [∼𝗚] ⊢[T.alt]! □⊥ :=
      provableₐ_D2_context (provableₐ_D2_context (of'! <| provableₐ_D1 <| CNC!) bew_not_bew_G) bew_bew_G
    simpa [provable₀_iff] using CN!_of_CN!_left (deduct'! this)
  · have : [□⊥] ⊢[T.alt]! □𝗚 := by
      have : T ⊢!. □(⊥ ➝ 𝗚) := provableₐ_D1 efq!
      exact provableₐ_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T.alt]! ∼𝗚 :=
      of'! (CN!_of_CN!_right <| K!_left <| goedel_iff_unprovable_goedel) ⨀ this
    simpa [provable₀_iff] using  CN!_of_CN!_right (deduct'! this)

/-- Gödel's Second Incompleteness Theorem-/
theorem goedel_second_incompleteness [Entailment.Consistent T] : T ⊬ ↑𝗖𝗼𝗻 := fun h ↦
  goedel_unprovable T <| K!_left (consistent_iff_goedel T) ⨀ h

theorem inconsistent_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑𝗖𝗼𝗻 := fun h ↦
  not_goedel_unprovable T <| contra! (K!_right (consistent_iff_goedel T)) ⨀ h

theorem inconsistent_undecidable [ℕ ⊧ₘ* T] : Entailment.Undecidable T ↑𝗖𝗼𝗻 := by
  haveI : Consistent T := Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩
  constructor
  · exact goedel_second_incompleteness T
  · exact inconsistent_unprovable T

instance [Entailment.Consistent T] : T ⪱ T + 𝐂𝐨𝐧[T] :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable (φ := ↑𝗖𝗼𝗻)
    (goedel_second_incompleteness T) (Entailment.by_axm _ (by simp))

instance [Entailment.Consistent T] : ℕ ⊧ₘ* 𝐂𝐨𝐧[T] := by
  suffices ℕ ⊧ₘ₀ T.consistentₐ by simpa [Models₀] using this
  suffices ¬T.Provableₐ ⌜⊥⌝ by simpa [models₀_iff] using  this
  intro H
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  have : T ⊢! ⊥ := provableₐ_iff_provable₀.mp H
  have : Entailment.Inconsistent T := inconsistent_iff_provable_bot.mpr this
  exact Consistent.not_inconsistent this

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + 𝐂𝐨𝐧[T] :=
  haveI : Entailment.Consistent T := Sound.consistent_of_satisfiable ⟨_, inferInstanceAs (ℕ ⊧ₘ* T)⟩
  ModelsTheory.add_iff.mpr ⟨inferInstance, inferInstance⟩

instance [ℕ ⊧ₘ* T] : T ⪱ T + ¬𝐂𝐨𝐧[T] :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑𝗖𝗼𝗻)
    (inconsistent_unprovable T) (Entailment.by_axm _ (by simp))

end

end LO.ISigma1
