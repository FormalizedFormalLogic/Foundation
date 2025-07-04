import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Gödel's second incompleteness theorem over $\mathsf{I}\Sigma_1$

-/

namespace LO.ISigma1

open FirstOrder Arith PeanoMinus IOpen ISigma0 Metamath Arithmetization
  Entailment FiniteContext

variable (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T] [T.Delta1Definable]

local notation "𝗚" => T.goedelₐ

local notation "𝗖𝗼𝗻" => T.consistentₐ

local prefix:max "□" => T.bewₐ

lemma goedel_iff_unprovable_goedel' : T ⊢! ↑𝗚 ⭤ ∼↑□𝗚 := by
  simpa [Axiom.provable_iff] using goedel_iff_unprovable_goedel

lemma goedel_unprovable [Entailment.Consistent T] : T ⊬ ↑𝗚 := by
  intro h
  have hp : T ⊢! ↑□𝗚 := (Axiom.provable_iff (T := T)).mp <| provableₐ_D1 <| (Axiom.provable_iff (T := T)).mpr h
  have hn : T ⊢! ∼↑□𝗚 := by simpa [Axiom.provable_iff] using K!_left (goedel_iff_unprovable_goedel' T) ⨀ h
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable hp hn) inferInstance

lemma not_goedel_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑𝗚 := fun h ↦ by
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  have : T ⊢!. □𝗚 := Entailment.CN!_of_CN!_left (K!_right goedel_iff_unprovable_goedel) ⨀ (by simpa [Axiom.provable_iff] using h)
  have : T ⊢! ↑𝗚 := (Axiom.provable_iff (T := T)).mp <| provableₐ_sound this
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h)
    (Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩)

lemma consistent_iff_goedel : T ⊢! ↑𝗖𝗼𝗻 ⭤ ↑𝗚 := by
  apply E!_intro
  · have bew_G : [∼𝗚] ⊢[T.toAxiom]! □𝗚 := deductInv'! <| CN!_of_CN!_left <| K!_right goedel_iff_unprovable_goedel
    have bew_not_bew_G : [∼𝗚] ⊢[T.toAxiom]! □(∼□𝗚) := by
      have : T ⊢!. □(𝗚 ➝ ∼□𝗚) := provableₐ_D1 <| K!_left goedel_iff_unprovable_goedel
      exact provableₐ_D2_context (of'! this) bew_G
    have bew_bew_G : [∼𝗚] ⊢[T.toAxiom]! □□𝗚 := provableₐ_D3_context bew_G
    have : [∼𝗚] ⊢[T.toAxiom]! □⊥ :=
      provableₐ_D2_context (provableₐ_D2_context (of'! <| provableₐ_D1 <| CNC!) bew_not_bew_G) bew_bew_G
    simpa [Axiom.provable_iff] using CN!_of_CN!_left (deduct'! this)
  · have : [□⊥] ⊢[T.toAxiom]! □𝗚 := by
      have : T ⊢!. □(⊥ ➝ 𝗚) := provableₐ_D1 efq!
      exact provableₐ_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T.toAxiom]! ∼𝗚 :=
      of'! (CN!_of_CN!_right <| K!_left <| goedel_iff_unprovable_goedel) ⨀ this
    simpa [Axiom.provable_iff] using  CN!_of_CN!_right (deduct'! this)

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
  have : T ⊢! ⊥ := (Axiom.provable_iff (T := T)).mp <| provableₐ_iff_provable₀.mp H
  have : Entailment.Inconsistent T := inconsistent_iff_provable_bot.mpr this
  exact Consistent.not_inconsistent this

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + 𝐂𝐨𝐧[T] :=
  haveI : Entailment.Consistent T := Sound.consistent_of_satisfiable ⟨_, inferInstanceAs (ℕ ⊧ₘ* T)⟩
  ModelsTheory.add_iff.mpr ⟨inferInstance, inferInstance⟩

instance [ℕ ⊧ₘ* T] : T ⪱ T + ¬𝐂𝐨𝐧[T] :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑𝗖𝗼𝗻)
    (inconsistent_unprovable T) (Entailment.by_axm _ (by simp))

end LO.ISigma1
