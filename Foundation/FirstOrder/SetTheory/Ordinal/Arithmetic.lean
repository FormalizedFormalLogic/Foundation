module

public import Foundation.FirstOrder.SetTheory.Ordinal.Basic
public import Foundation.FirstOrder.SetTheory.Recursion

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

namespace IsOrdinal

open IsOrdinal

variable {α β γ : V}

/-! ### Ordinal addition (initial/successor stage) -/

section ordinalAddition


/-- Successor-step function used for ordinal addition recursion. -/
noncomputable def OrdinalAddSuccStep (x : V) : V := succ x

instance ordinalAddSuccStep_definable :
    ℒₛₑₜ-function₁[V] OrdinalAddSuccStep := by
  show ℒₛₑₜ-function₁[V] (fun x ↦ succ x)
  definability

lemma ordinalAddSuccStep_strict :
    ∀ x : V, x ∈ OrdinalAddSuccStep x := by
  intro x
  simp [OrdinalAddSuccStep]

lemma ordinalAddSuccStep_extend :
    ∀ u x : V, u ∈ x → u ∈ OrdinalAddSuccStep x := by
  intro u x hux
  simp [OrdinalAddSuccStep, mem_succ_iff, hux]

variable [V ⊧ₘ* 𝗭𝗙]

/--
Set-level ordinal-addition value obtained by specialized transfinite recursion:
base value `a`, successor step `succ`, and limit step `⋃ˢ range`.
-/
noncomputable def ordinalAddValue (a b : V) : V :=
  transfiniteRecursionValueFn (SuccLimitRecursionStep a OrdinalAddSuccStep) b

lemma ordinalAddValue_isRecursionValueOfFunction (a b : V) (hb : IsOrdinal b) :
    IsTransfiniteRecursionValueOfFunction
      (SuccLimitRecursionStep a OrdinalAddSuccStep) b (ordinalAddValue a b) := by
  exact (isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
    (F := SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable)
    hb).2 rfl

omit [V ⊧ₘ* 𝗭𝗙] in
private instance ordinalAddSuccStep_definable_step :
    ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep a OrdinalAddSuccStep) :=
  succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable (a : V) :
    ℒₛₑₜ-function₁[V] (ordinalAddValue a) :=
  transfiniteRecursionValueFn_definable
    (F := SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable_varInit :
    ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
  transfiniteRecursionValueFnVar_definable
    (Φ := fun a ↦ SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable_varInit
      (F := OrdinalAddSuccStep) ordinalAddSuccStep_definable)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable_left (b : V) :
    ℒₛₑₜ-function₁[V] (fun a ↦ ordinalAddValue a b) := by
  letI : ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
    ordinalAddValue_definable_varInit
  definability

@[simp] lemma ordinalAddValue_zero (a : V) :
    ordinalAddValue a 0 = a := by
  simp only [ordinalAddValue]
  -- transfiniteRecursionValueFn (SuccLimitRecursionStep a OrdinalAddSuccStep) 0
  -- = (SuccLimitRecursionStep a OrdinalAddSuccStep) (attemptOrDefault ... 0)
  -- The recursion function at 0 is ∅, so SuccLimitRecursionStep on ∅ = a₀ = a.
  unfold transfiniteRecursionValueFn
  have hSdef : ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep a OrdinalAddSuccStep) :=
    ordinalAddSuccStep_definable_step
  let αo : Ordinal V := IsOrdinal.toOrdinal (0 : V)
  have hrf : IsAttemptGraph (SuccLimitRecursionStep a OrdinalAddSuccStep) 0
      (attemptOrDefault (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on
        (F := SuccLimitRecursionStep a OrdinalAddSuccStep) hSdef αo
  have hdom : domain (attemptOrDefault
      (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) = (0 : V) := hrf.2.2.1
  have hdomEmpty : domain (attemptOrDefault
      (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) = (∅ : V) := by
    simpa [zero_def] using hdom
  simp [SuccLimitRecursionStep, hdomEmpty]

@[simp] lemma ordinalAddValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalAddValue a (succ β) =
      succ (ordinalAddValue a β) := by
  simp only [ordinalAddValue]
  exact succLimitRecursionStep_successor_transfiniteRecursionValueFn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable hβ

lemma ordinalAddValue_isOrdinal
    (a β : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) :
    IsOrdinal (ordinalAddValue a β) := by
  simp only [ordinalAddValue]
  exact succLimitRecursion_stageValue_isOrdinal_fn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable ha
    (fun x hx ↦ by simp only [OrdinalAddSuccStep]; exact IsOrdinal.succ (α := x))
    (IsOrdinal.succ (α := β)) β (by simp)

lemma ordinalAddValue_strictIncreasing_right
    (a : V) {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalAddValue a β ∈ ordinalAddValue a γ := by
  simp only [ordinalAddValue]
  exact succLimitRecursion_strictIncreasing_fn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable
    ordinalAddSuccStep_strict ordinalAddSuccStep_extend
    (IsOrdinal.succ (α := γ)) β γ hβγ (by simp)

lemma ordinalAddValue_subset_right_of_initOrdinal
    (a β γ : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) (hγ : IsOrdinal γ)
    (hβγ : β ⊆ γ) :
    ordinalAddValue a β ⊆ ordinalAddValue a γ := by
  by_cases hEq : β = γ
  · subst hEq
    simp
  · have hβmemγ : β ∈ γ := (IsOrdinal.ssubset_iff (α := β) (β := γ)).1 ⟨hβγ, hEq⟩
    have hlt : ordinalAddValue a β ∈ ordinalAddValue a γ :=
      ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ) (hβγ := hβmemγ)
    have hγord' : IsOrdinal (ordinalAddValue a γ) :=
      ordinalAddValue_isOrdinal a γ ha hγ
    exact hγord'.toIsTransitive.transitive _ hlt

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_le
    (a : V) {α f : V}
    (hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    {γ : V} (hγ : IsOrdinal γ) (hale : a ⊆ γ) (hsuccγα : succ γ ∈ α) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ ⊆ γ ∧
      ∀ η yη, η ∈ α → ⟨η, yη⟩ₖ ∈ f → yη ⊆ γ → η ⊆ δ :=
  succLimitRecursion_exists_max_stage_le
    (a₀ := a) (F := OrdinalAddSuccStep)
    hrec hstrict hValOrd hself hγ hale hsuccγα

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_eq
    (a : V) {γ α f : V}
    (hαeq : α = succ (succ γ))
    (hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    (hγ : IsOrdinal γ) (hale : a ⊆ γ) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ = γ ∧
      ∀ η yη, η ∈ α → ⟨η, yη⟩ₖ ∈ f → yη ⊆ γ → η ⊆ δ := by
  have hsuccγα : succ γ ∈ α := by rw [hαeq]; simp
  rcases ordinalAddRecursion_exists_max_right_le
      (a := a) (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hγ := hγ) (hale := hale) (hsuccγα := hsuccγα) with
    ⟨δ, yδ, hδα, hδyδ, hyδle, hmax⟩
  obtain ⟨hαord, hfFunc, hfDom, hfRec⟩ := hrec
  letI : IsFunction f := hfFunc
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  by_cases hEq : yδ = γ
  · refine ⟨δ, yδ, hδα, hδyδ, hEq, hmax⟩
  · have hyδγ : yδ ∈ γ := by
      letI : IsOrdinal yδ := hyδord
      letI : IsOrdinal γ := hγ
      rcases IsOrdinal.subset_iff (α := yδ) (β := γ) |>.1 hyδle with (h | h)
      · exact (hEq h).elim
      · exact h
    have hδ_sub_yδ : δ ⊆ yδ := hself δ yδ hδα hδyδ
    have hδ_sub_γ : δ ⊆ γ := subset_trans hδ_sub_yδ (hγ.toIsTransitive.transitive _ hyδγ)
    have hδγ : δ ∈ γ := by
      letI : IsOrdinal δ := hδord
      letI : IsOrdinal γ := hγ
      rcases IsOrdinal.subset_iff (α := δ) (β := γ) |>.1 hδ_sub_γ with (hEq' | hMem')
      · rw [hEq'] at hδ_sub_yδ
        exact ((mem_irrefl yδ) (hδ_sub_yδ _ hyδγ)).elim
      · exact hMem'
    have hsuccδ_sub_γ : succ δ ⊆ γ := by
      intro t ht
      rcases show t = δ ∨ t ∈ δ by simpa [mem_succ_iff] using ht with (rfl | htδ)
      · exact hδγ
      · exact hγ.toIsTransitive.transitive _ hδγ _ htδ
    have hsuccδ_in_succγ : succ δ ∈ succ γ := by
      simp only [mem_succ_iff]
      haveI : IsOrdinal (succ δ) := IsOrdinal.succ
      haveI : IsOrdinal γ := hγ
      exact (IsOrdinal.subset_iff (α := succ δ) (β := γ)).1 hsuccδ_sub_γ
    have hsuccδ_in_α : succ δ ∈ α :=
      hαord.toIsTransitive.transitive _ hsuccγα _ hsuccδ_in_succγ
    have hsucc_sub_α : succ δ ⊆ α := hαord.toIsTransitive.transitive _ hsuccδ_in_α
    rcases mem_domain_iff.mp (by rw [hfDom]; exact hsuccδ_in_α) with ⟨yS, hsuccδyS⟩
    have hyS_rule : SuccLimitRecursionRule a OrdinalAddSuccStep yS (f ↾ (succ δ)) :=
      (hfRec (succ δ) hsuccδ_in_α yS).1 hsuccδyS
    have hdom_succδ : domain (f ↾ (succ δ)) = succ δ := by
      simp [domain_restrict_eq, hfDom, inter_eq_right_of_subset hsucc_sub_α]
    have hyS_eq : yS = succ yδ := by
      rcases hyS_rule with (h0 | hs | hL)
      · have : succ δ = (∅ : V) := by simpa [hdom_succδ] using h0.1
        have : δ ∈ (∅ : V) := by simpa [this] using (show δ ∈ succ δ by simp)
        exact (not_mem_empty this).elim
      · rcases hs with ⟨δ', x, hdb, hδ'x, hxyS⟩
        have hdb' : succ δ' = succ δ := by simpa [hdom_succδ] using hdb.symm
        have : δ' = δ := succ_inj hdb'
        rw [this] at hδ'x
        have hδx : ⟨δ, x⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδ'x).1
        have : x = yδ := IsFunction.unique hδx hδyδ
        subst this
        have h := hxyS
        simp only [OrdinalAddSuccStep] at h
        exact h
      · exact (hL.2.1 δ (by simp [hdom_succδ])).elim
    have hySle : yS ⊆ γ := by
      have hsuccyδ_sub_γ : succ yδ ⊆ γ := by
        intro t ht
        rcases show t = yδ ∨ t ∈ yδ by simpa [mem_succ_iff] using ht with (rfl | htyδ)
        · exact hyδγ
        · exact hγ.toIsTransitive.transitive _ hyδγ _ htyδ
      simpa [hyS_eq] using hsuccyδ_sub_γ
    have hsuccδ_sub_δ : succ δ ⊆ δ := hmax (succ δ) yS hsuccδ_in_α hsuccδyS hySle
    have : δ ∈ δ := hsuccδ_sub_δ _ (by simp)
    exact ((mem_irrefl δ) this).elim

lemma ordinalAddValue_exists_right_eq_of_subset
    (a γ : V) (ha : IsOrdinal a) (hγ : IsOrdinal γ) (hale : a ⊆ γ) :
    ∃ δ : Ordinal V, ordinalAddValue a δ.val = γ := by
  let G : V → V := SuccLimitRecursionStep a OrdinalAddSuccStep
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable
  let f : V := attemptOrDefault G (succ (succ γ))
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Convert the function-graph recursion for `G` into the specialized rule recursion.
  have hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f := by
    -- TODO: This looks similar to earlier code, is it compressible?
    letI : IsFunction f := hfRecGraph.2.1
    refine ⟨hα, hfRecGraph.2.1, hfRecGraph.2.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      hfRecGraph.2.2.2 β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a OrdinalAddSuccStep (SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a OrdinalAddSuccStep (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a OrdinalAddSuccStep (SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a OrdinalAddSuccStep (hr := IsFunction.restrict _ _)
      have hyEq :
          y = SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β) :=
        (succLimitRecursionRule_functionLike a OrdinalAddSuccStep (f ↾ β) (IsFunction.restrict _ _)).unique
          hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := a) (F := OrdinalAddSuccStep)
      ordinalAddSuccStep_strict ordinalAddSuccStep_extend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := a) (F := OrdinalAddSuccStep) ha
      (by
        intro x hx
        simp only [OrdinalAddSuccStep]
        exact IsOrdinal.succ (α := x))
      hrec
  have hAddDef : ℒₛₑₜ-function₁[V] (ordinalAddValue a) := ordinalAddValue_definable a
  have hstrictRel :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalAddValue a β) → (yγ = ordinalAddValue a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl
    rcases hyγ with rfl
    exact ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ') (hβγ := hβγ)
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    have hyeqAdd : y = ordinalAddValue a β := by simpa [G, ordinalAddValue] using hy
    have hnot : ¬ y ∈ β := by
      intro hyβ
      have hnotAdd := strictIncreasing_function_no_value_lt_self
        (F := ordinalAddValue a)
        (hFdef := hAddDef)
        (hFstrict := by
          intro β' γ' hβ' hγ' hβγ'
          exact ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ') (hβγ := hβγ'))
        β hβord
      exact hnotAdd (by simpa [hyeqAdd] using hyβ)
    letI : IsOrdinal β := hβord
    letI : IsOrdinal y := hyord
    rcases IsOrdinal.mem_trichotomy (α := y) (β := β) with (hyβ | hEq | hβy)
    · exact (hnot hyβ).elim
    · simp [hEq]
    · exact (IsOrdinal.subset_iff (α := β) (β := y)).2 (Or.inr hβy)
  rcases ordinalAddRecursion_exists_max_right_eq
      (a := a) (γ := γ) (α := α) (f := f) (hαeq := rfl)
      (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hγ := hγ) (hale := hale) with
    ⟨δ, yδ, hδα, hδyδ, hyδeqγ, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδ : yδ = transfiniteRecursionValueFn G δ :=
    (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hδα).1 hδyδ
  have hyδeqAdd : yδ = ordinalAddValue a δ := by simpa [G, ordinalAddValue] using hyδ
  refine ⟨⟨δ, hδord⟩, ?_⟩
  simpa [hyδeqγ] using hyδeqAdd.symm

end ordinalAddition

end IsOrdinal

namespace Ordinal

variable [V ⊧ₘ* 𝗭𝗙]

/--
Current set-level value of ordinal addition.
This is the first stage of ordinal arithmetic development: base and successor equations.
-/
noncomputable def addValue (α β : Ordinal V) : V :=
  IsOrdinal.ordinalAddValue α.val β.val

@[simp] lemma addValue_bot (α : Ordinal V) : addValue α ⊥ = α.val := by
  simp only [addValue, bot_val_eq]
  exact IsOrdinal.ordinalAddValue_zero (a := α.val)

@[simp] lemma addValue_succ (α β : Ordinal V) :
    addValue α β.succ = succ (addValue α β) := by
  simp [addValue, succ_val]

lemma addValue_strictIncreasing_right (α : Ordinal V) {β γ : Ordinal V} (hβγ : β < γ) :
    addValue α β ∈ addValue α γ := by
  simpa [addValue] using
    IsOrdinal.ordinalAddValue_strictIncreasing_right (a := α.val) (hγ := γ.ordinal) (hβγ := hβγ)

end Ordinal

namespace IsOrdinal

variable {α β γ : V}

/-! ### Ordinal multiplication (initial/successor stage) -/

section ordinalMultiplication

variable [V ⊧ₘ* 𝗭𝗙]

/-- Successor-step function for right-multiplication by `a`: maps `x` to `x + a`. -/
noncomputable def OrdinalMulSuccStep (a x : V) : V := ordinalAddValue x a

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulSuccStep_definable (a : V) :
    ℒₛₑₜ-function₁[V] (OrdinalMulSuccStep a) := by
  show ℒₛₑₜ-function₁[V] (fun x ↦ ordinalAddValue x a)
  exact ordinalAddValue_definable_left a

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulSuccStep_definable_varLeft :
    ℒₛₑₜ-function₂[V] (fun a x ↦ OrdinalMulSuccStep a x) := by
  show ℒₛₑₜ-function₂[V] (fun a x ↦ ordinalAddValue x a)
  letI : ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
    ordinalAddValue_definable_varInit
  definability

lemma ordinalMulSuccStep_strict_of_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) :
    ∀ x : V, x ∈ OrdinalMulSuccStep a x := by
  intro x
  simp only [OrdinalMulSuccStep]
  have hxlt : ordinalAddValue x 0 ∈ ordinalAddValue x a :=
    ordinalAddValue_strictIncreasing_right (a := x) (hγ := ha) (hβγ := ha0)
  simpa using hxlt

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalMulSuccStep_extend_of_pos
    (a : V)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x) :
    ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x := hStepExtend

/--
Set-level ordinal multiplication value (as recursion in the right argument):
base value `0`, successor step `x ↦ x + a`, and limit step `⋃ˢ range`.
-/
noncomputable def ordinalMulValue (a b : V) : V :=
  transfiniteRecursionValueFn (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) b

omit [V ⊧ₘ* 𝗭𝗙] in
private instance ordinalMulSuccStep_definable_step (a : V) :
    ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) :=
  succLimitRecursionStep_definable (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulValue_definable (a : V) :
    ℒₛₑₜ-function₁[V] (ordinalMulValue a) :=
  transfiniteRecursionValueFn_definable
    (F := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a))
    (ordinalMulSuccStep_definable_step a)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulValue_definable_varInit :
    ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalMulValue a b) :=
  transfiniteRecursionValueFnVar_definable
    (Φ := fun a ↦ SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a))
    (succLimitRecursionStep_definable_varF (0 : V)
      (F := fun a ↦ OrdinalMulSuccStep a) ordinalMulSuccStep_definable_varLeft)

@[simp] lemma ordinalMulValue_zero (a : V) :
    ordinalMulValue a 0 = (0 : V) := by
  simp only [ordinalMulValue]
  unfold transfiniteRecursionValueFn
  have hSdef : ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) :=
    ordinalMulSuccStep_definable_step a
  let αo : Ordinal V := IsOrdinal.toOrdinal (0 : V)
  have hrf : IsAttemptGraph (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0
      (attemptOrDefault (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on
        (F := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) hSdef αo
  have hdom : domain (attemptOrDefault
      (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) = (0 : V) := hrf.2.2.1
  have hdomEmpty : domain (attemptOrDefault
      (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) = (∅ : V) := by
    simpa [zero_def] using hdom
  simp [SuccLimitRecursionStep, hdomEmpty]

@[simp] lemma ordinalMulValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalMulValue a (succ β) =
      ordinalAddValue (ordinalMulValue a β) a := by
  simp only [ordinalMulValue]
  exact succLimitRecursionStep_successor_transfiniteRecursionValueFn
    (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a) hβ

lemma ordinalMulValue_strictIncreasing_right_of_left_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x)
    {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalMulValue a β ∈ ordinalMulValue a γ := by
  simp only [ordinalMulValue]
  exact succLimitRecursion_strictIncreasing_fn
    (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)
    (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend
    (IsOrdinal.succ (α := γ)) β γ hβγ (by simp)

lemma ordinalMulValue_exists_right_mul_add_eq_of_pos
    (a γ : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) (hγ : IsOrdinal γ)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x) :
    ∃ δ ρ : Ordinal V,
      ordinalAddValue (ordinalMulValue a δ.val) ρ.val = γ ∧
      ρ.val ∈ a := by
  let G : V → V := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)
  have hGdef : ℒₛₑₜ-function₁[V] G := ordinalMulSuccStep_definable_step a
  let f : V := attemptOrDefault G (succ (succ γ))
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := G) hGdef αo
  have hrec : IsAttempt
      (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) α f := by
    -- TODO: This looks similar to earlier code, is it compressible?
    letI : IsFunction f := hfRecGraph.2.1
    refine ⟨hα, hfRecGraph.2.1, hfRecGraph.2.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      hfRecGraph.2.2.2 β hβα y
    constructor
    · intro hβy
      have hyEq : y = SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a) (f ↾ β) := by
        simpa [G, Function.Graph] using hiffG.1 hβy
      have hstep := succLimitRecursionStep_spec (0 : V) (OrdinalMulSuccStep a)
        (hr := IsFunction.restrict f β)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep := succLimitRecursionStep_spec (0 : V) (OrdinalMulSuccStep a)
        (hr := IsFunction.restrict f β)
      have hyEq := (succLimitRecursionRule_functionLike (0 : V) (OrdinalMulSuccStep a)
        (f ↾ β) (IsFunction.restrict f β)).unique hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a) (by infer_instance)
      (by
        intro x hx
        simp only [OrdinalMulSuccStep]
        exact ordinalAddValue_isOrdinal x a hx ha)
      hrec
  have hMulDef : ℒₛₑₜ-function₁[V] (ordinalMulValue a) := ordinalMulValue_definable a
  have hstrictRel :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalMulValue a β) → (yγ = ordinalMulValue a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl; rcases hyγ with rfl
    exact ordinalMulValue_strictIncreasing_right_of_left_pos
      (a := a) (ha := ha) (ha0 := ha0) (hStepExtend := hStepExtend) (hγ := hγ') (hβγ := hβγ)
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hyeqMul : y = ordinalMulValue a β := by
      simpa [G, ordinalMulValue] using
        (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
          (F := G) hGdef hα hβα).1 hβy
    have hnot : ¬ y ∈ β := by
      intro hyβ
      exact (strictIncreasing_function_no_value_lt_self
        (F := ordinalMulValue a)
        (hFdef := hMulDef)
        (hFstrict := by
          intro β' γ' hβ' hγ' hβγ'
          exact ordinalMulValue_strictIncreasing_right_of_left_pos
            (a := a) (ha := ha) (ha0 := ha0) (hStepExtend := hStepExtend) (hγ := hγ') (hβγ := hβγ'))
        β hβord) (by simpa [hyeqMul] using hyβ)
    letI : IsOrdinal β := hβord; letI : IsOrdinal y := hyord
    rcases IsOrdinal.mem_trichotomy (α := y) (β := β) with (hyβ | hEq | hβy)
    · exact (hnot hyβ).elim
    · simp [hEq]
    · exact (IsOrdinal.subset_iff (α := β) (β := y)).2 (Or.inr hβy)
  have hsuccγα : succ γ ∈ α := by simp [α]
  rcases succLimitRecursion_exists_max_stage_le
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a)
      (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hξord := hγ) (ha₀le := empty_subset γ) (hsuccξα := hsuccγα) with
    ⟨δ, yδ, hδα, hδyδ, hyδleγ, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  rcases ordinalAddValue_exists_right_eq_of_subset yδ γ hyδord hγ hyδleγ with ⟨ρ, hρeq⟩
  have hρord : IsOrdinal ρ.val := ρ.ordinal
  by_cases hρlt : ρ.val ∈ a
  · have hyδeqMul : yδ = ordinalMulValue a δ := by
      simpa [G, ordinalMulValue] using
        (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
          (F := G) hGdef hα hδα).1 hδyδ
    refine ⟨⟨δ, hδord⟩, ρ, ?_, hρlt⟩
    simpa [hyδeqMul] using hρeq
  · have ha_sub_ρ : a ⊆ ρ.val := by
      letI : IsOrdinal a := ha; letI : IsOrdinal ρ.val := hρord
      rcases IsOrdinal.mem_trichotomy (α := ρ.val) (β := a) with (hρa | hEq | haρ)
      · exact (hρlt hρa).elim
      · simp [hEq]
      · exact hρord.toIsTransitive.transitive _ haρ
    have hsuccδ_in_α : succ δ ∈ α := by
      have hδ_sub_γ : δ ⊆ γ := subset_trans (hself δ yδ hδα hδyδ) hyδleγ
      letI : IsOrdinal δ := hδord; letI : IsOrdinal γ := hγ
      rcases (IsOrdinal.subset_iff (α := δ) (β := γ)).1 hδ_sub_γ with (hEq | hMem)
      · rw [hEq]; exact hsuccγα
      · have hsuccδ_sub_γ : succ δ ⊆ γ := by
          intro t ht
          rcases show t = δ ∨ t ∈ δ by simpa [mem_succ_iff] using ht with (rfl | htδ)
          · exact hMem
          · exact hγ.toIsTransitive.transitive _ hMem _ htδ
        haveI : IsOrdinal (succ δ) := IsOrdinal.succ
        rcases (IsOrdinal.subset_iff (α := succ δ) (β := γ)).1 hsuccδ_sub_γ with (hEq' | hMem')
        · rw [hEq']; exact hα.toIsTransitive.transitive _ hsuccγα _ (by simp)
        · exact hα.toIsTransitive.transitive _ hsuccγα _ (by simp [mem_succ_iff, hMem'])
    have hsucc_sub_α : succ δ ⊆ α := hα.toIsTransitive.transitive _ hsuccδ_in_α
    rcases mem_domain_iff.mp (by rw [hfRecGraph.2.2.1]; exact hsuccδ_in_α) with ⟨yS, hsuccδyS⟩
    have hySrule :=
      (hrec.2.2.2 (succ δ) hsuccδ_in_α yS).1 hsuccδyS
    have hdom_succδ : domain (f ↾ (succ δ)) = succ δ := by
      simp only [domain_restrict_eq, hfRecGraph.2.2.1, inter_eq_right_of_subset hsucc_sub_α]
    have hyS_eq_add : yS = ordinalAddValue yδ a := by
      rcases hySrule with (h0 | hs | hL)
      · have : succ δ = (∅ : V) := by simpa [hdom_succδ] using h0.1
        have hδsucc : δ ∈ succ (V := V) δ := by simp
        have hδempty : δ ∈ (∅ : V) := by simpa only [this] using hδsucc
        exact (not_mem_empty hδempty).elim
      · rcases hs with ⟨δ', x, hdom', hδ'x, hxyS⟩
        have hδ' : δ' = δ := succ_inj (by simpa [hdom_succδ] using hdom'.symm)
        rw [hδ'] at hδ'x
        haveI : IsFunction f := hfRecGraph.2.1
        have hx_eq : x = yδ := IsFunction.unique (kpair_mem_restrict_iff.mp hδ'x).1 hδyδ
        subst hx_eq; exact hxyS
      · exact (hL.2.1 δ (by simp [hdom_succδ])).elim
    have hyS_sub_γ : yS ⊆ γ := by
      have : ordinalAddValue yδ a ⊆ ordinalAddValue yδ ρ.val :=
        ordinalAddValue_subset_right_of_initOrdinal yδ a ρ.val hyδord ha hρord ha_sub_ρ
      simpa [hyS_eq_add, hρeq] using this
    have hsuccδ_sub_δ : succ δ ⊆ δ := hmax (succ δ) yS hsuccδ_in_α hsuccδyS hyS_sub_γ
    exact (mem_irrefl δ (hsuccδ_sub_δ _ (by simp))).elim

end ordinalMultiplication

end IsOrdinal

namespace Ordinal

variable [V ⊧ₘ* 𝗭𝗙]

/-- Current set-level value of ordinal multiplication. -/
noncomputable def mulValue (α β : Ordinal V) : V :=
  IsOrdinal.ordinalMulValue α.val β.val

@[simp] lemma mulValue_bot (α : Ordinal V) : mulValue α ⊥ = (0 : V) := by
  simp only [mulValue, bot_val_eq]
  exact IsOrdinal.ordinalMulValue_zero (a := α.val)

@[simp] lemma mulValue_succ (α β : Ordinal V) :
    mulValue α β.succ = IsOrdinal.ordinalAddValue (mulValue α β) α.val := by
  simp [mulValue, succ_val]

end Ordinal
