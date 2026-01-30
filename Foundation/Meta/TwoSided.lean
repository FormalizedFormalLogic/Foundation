module

public import Foundation.Propositional.Entailment.Cl.Basic

@[expose] public section

namespace LO.Entailment

open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F] {S : Type*} [Entailment S F]

variable (𝓢 : S)

abbrev TwoSided (Γ Δ : List F) : Prop := Γ ⊢[𝓢] Δ.disj

variable {𝓢} [Entailment.Int 𝓢]

local notation:40 Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

namespace TwoSided

variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : List F} {φ ψ χ : F}

lemma weakening (h : Γ₁ ⟹ Δ₁) (HΓ : Γ₁ ⊆ Γ₂ := by simp) (HΔ : Δ₁ ⊆ Δ₂ := by simp) : Γ₂ ⟹ Δ₂ :=
  FiniteContext.weakening! HΓ <| left_Disj!_intro Δ₁ (fun _ hψ ↦ right_Disj!_intro _ (HΔ hψ)) ⨀! h

lemma remove_left (hφ : Γ ⟹ Δ) : φ :: Γ ⟹ Δ := weakening hφ

lemma remove_right (hφ : Γ ⟹ Δ) : Γ ⟹ φ :: Δ := weakening hφ

lemma rotate_right (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := weakening hφ

lemma rotate_left (hφ : (Γ ++ [φ]) ⟹ Δ) : (φ :: Γ) ⟹ Δ := weakening hφ

lemma rotate_right_inv (hφ : Γ ⟹ φ :: Δ) : Γ ⟹ Δ ++ [φ] := weakening hφ

lemma rotate_left_inv (hφ : (φ :: Γ) ⟹ Δ) : (Γ ++ [φ]) ⟹ Δ := weakening hφ

lemma to_provable {φ} (h : [] ⟹ [φ]) : 𝓢 ⊢ φ :=
  FiniteContext.provable_iff_provable.mpr <| left_Disj!_intro [φ] (by simp) ⨀! h

lemma add_hyp {𝒯 : S} [𝒯 ⪯ 𝓢] (hφ : 𝒯 ⊢ φ) (h : (φ :: Γ) ⟹ Δ) : Γ ⟹ Δ :=
  deduct! h ⨀! of'! (WeakerThan.pbl hφ)

lemma right_closed (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := right_Disj!_intro _ (φ := φ) (by simp) ⨀! (by_axm! h)

lemma left_closed (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := right_Disj!_intro _ (φ := φ) h ⨀! by_axm!

lemma verum_right : Γ ⟹ ⊤ :: Δ := right_Disj!_intro _ (φ := ⊤) (by simp) ⨀! (by simp)

omit [DecidableEq F] in
lemma falsum_left : (⊥ :: Γ) ⟹ Δ := efq! ⨀! by_axm₀!

lemma falsum_right (h : Γ ⟹ Δ) : Γ ⟹ ⊥ :: Δ := weakening h

lemma verum_left (h : Γ ⟹ Δ) : (⊤ :: Γ) ⟹ Δ := weakening h

lemma and_right (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ⟹ Δ ++ [ψ]) : Γ ⟹ φ ⋏ ψ :: Δ := by
  have : Γ ⊢[𝓢] (φ :: Δ).disj ➝ (ψ :: Δ).disj ➝ (φ ⋏ ψ :: Δ).disj := by
    apply left_Disj!_intro
    rintro χ hχ
    rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply deduct!
      apply left_Disj!_intro
      intro ξ hξ
      rcases show ξ = ψ ∨ ξ ∈ Δ by simpa using hξ with (rfl | hξ)
      · apply deduct!
        apply right_Disj!_intro (χ ⋏ ξ :: Δ) (φ := χ ⋏ ξ) List.mem_cons_self ⨀! (K!_intro by_axm₁! by_axm₀!)
      · apply right_Disj!_intro _ (by simp [hξ])
    · apply deduct!
      apply dhyp!
      apply right_Disj!_intro _ (φ := χ) (by simp [hχ]) ⨀! by_axm₀!
  exact this ⨀! weakening hφ ⨀! weakening hψ

lemma or_left (hφ : Γ ++ [φ] ⟹ Δ) (hψ : Γ ++ [ψ] ⟹ Δ) : φ ⋎ ψ :: Γ ⟹ Δ := by
  apply deductInv!
  apply left_A!_intro
  · apply deduct! <| weakening hφ
  · apply deduct! <| weakening hψ

lemma or_right (h : Γ ⟹ Δ ++ [φ, ψ]) : Γ ⟹ φ ⋎ ψ :: Δ := by
  have : Γ ⊢[𝓢] (φ :: ψ :: Δ).disj ➝ (φ ⋎ ψ :: Δ).disj := by
    apply left_Disj!_intro
    intro χ hχ
    rcases show χ = φ ∨ χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | rfl | hχ)
    · apply right_Disj!_intro' (χ ⋎ ψ :: Δ) (φ := χ ⋎ ψ) (by simp) or₁!
    · apply right_Disj!_intro' (φ ⋎ χ :: Δ) (φ := φ ⋎ χ) (by simp) or₂!
    · apply right_Disj!_intro _ (by simp [hχ])
  exact this ⨀! weakening h

lemma and_left (h : Γ ++ [φ, ψ] ⟹ Δ) : (φ ⋏ ψ :: Γ) ⟹ Δ := by
  have : φ :: ψ :: Γ ⟹ Δ := weakening h
  have : (φ ⋏ ψ :: Γ) ⊢[𝓢] ψ ➝ φ ➝ Δ.disj := wk! (by simp) (deduct! <| deduct! this)
  exact this ⨀! (deductInv! and₂!) ⨀! (deductInv! and₁!)

lemma neg_right_int (h : Γ ++ [φ] ⟹ []) : Γ ⟹ ∼φ :: Δ := by
  have : φ :: Γ ⟹ [] := weakening h
  have : Γ ⊢[𝓢] ∼φ := N!_iff_CO!.mpr <| deduct! this
  have : Γ ⟹ [∼φ] := (right_Disj!_intro _ (by simp)) ⨀! this
  exact weakening this

omit [Entailment.Int 𝓢] in
lemma neg_right_cl [Entailment.Cl 𝓢] (h : Γ ++ [φ] ⟹ Δ) : Γ ⟹ ∼φ :: Δ := by
  have hφ : Γ ⊢[𝓢] φ ➝ (∼φ :: Δ).disj := by
    apply deduct!
    suffices (φ :: Γ) ⊢[𝓢] Δ.disj ➝ (∼φ :: Δ).disj from this ⨀ weakening h
    apply left_Disj!_intro
    intro ψ hψ
    apply right_Disj!_intro _ (by simp [hψ])
  have hnφ : Γ ⊢[𝓢] ∼φ ➝ (∼φ :: Δ).disj := right_Disj!_intro _ (by simp)
  exact left_A!_intro hφ hnφ ⨀ lem!

lemma neg_left_int (h : Γ ++ [∼φ] ⟹ Δ ++ [φ]) : ∼φ :: Γ ⟹ Δ := by
  have h : ∼φ :: Γ ⟹ φ :: Δ := weakening h
  suffices (∼φ :: Γ) ⊢[𝓢] (φ :: Δ).disj ➝ Δ.disj from this ⨀ (wk! (by simp) h)
  apply left_Disj!_intro
  intro ψ hψ
  rcases show ψ = φ ∨ ψ ∈ Δ by simpa using hψ with (rfl | hψ)
  · apply deductInv!
    exact CNC!
  · apply right_Disj!_intro _ (by simp [hψ])

lemma neg_left (h : Γ ⟹ Δ ++ [φ]) : ∼φ :: Γ ⟹ Δ :=
  neg_left_int (weakening h)

lemma imply_left_int (hφ : Γ ++ [φ ➝ ψ] ⟹ Δ ++ [φ]) (hψ : Γ ++ [ψ] ⟹ Δ) : (φ ➝ ψ) :: Γ ⟹ Δ := by
  have hφ : (φ ➝ ψ) :: Γ ⟹ φ :: Δ := weakening hφ
  have hψ : ψ :: Γ ⟹ Δ := weakening hψ
  suffices ((φ ➝ ψ) :: Γ) ⊢[𝓢] (φ :: Δ).disj ➝ Δ.disj from this ⨀! wk! (by simp) hφ
  apply left_Disj!_intro
  intro χ hχ
  rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
  · apply deduct!
    have : Γ ⊢[𝓢] ψ ➝ Δ.disj := deduct! hψ
    apply (wk! (by simp) this) ⨀! (by_axm₁! ⨀! by_axm₀!)
  · apply right_Disj!_intro _ (by simp [hχ])

lemma imply_left (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ++ [ψ] ⟹ Δ) : (φ ➝ ψ) :: Γ ⟹ Δ :=
  imply_left_int (weakening hφ) (weakening hψ)

lemma imply_right_int (h : Γ ++ [φ] ⟹ [ψ]) : Γ ⟹ (φ ➝ ψ) :: Δ := by
  have h : φ :: Γ ⟹ [ψ] := weakening h
  have : (φ :: Γ) ⊢[𝓢] ψ := (left_Disj!_intro _ <| by simp) ⨀ h
  exact (right_Disj!_intro _ <| by simp) ⨀! deduct! this

omit [Entailment.Int 𝓢] in
lemma imply_right_cl [Entailment.Cl 𝓢] (h : Γ ++ [φ] ⟹ Δ ++ [ψ]) : Γ ⟹ (φ ➝ ψ) :: Δ := by
  have h : φ :: Γ ⟹ ψ :: Δ := weakening h
  have hnφ : Γ ⊢[𝓢] ∼φ ➝ ((φ ➝ ψ) :: Δ).disj := by
    apply right_Disj!_intro' ((φ ➝ ψ) :: Δ) (φ := φ ➝ ψ) (by simp)
    exact CNC!
  have hφ : Γ ⊢[𝓢] φ ➝ ((φ ➝ ψ) :: Δ).disj := by
    apply deduct!
    suffices (φ :: Γ) ⊢[𝓢] (ψ :: Δ).disj ➝ ((φ ➝ ψ) :: Δ).disj from this ⨀ h
    apply left_Disj!_intro
    intro χ hχ
    rcases show χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply right_Disj!_intro' _ (φ := φ ➝ χ) (by simp)
      exact implyK!
    · apply right_Disj!_intro
      simp [hχ]
  exact left_A!_intro hφ hnφ ⨀ lem!

omit [Entailment.Int 𝓢] in
lemma iff_right_cl [Entailment.Cl 𝓢] (hr : Γ ++ [φ] ⟹ Δ ++ [ψ]) (hl : Γ ++ [ψ] ⟹ Δ ++ [φ]) : Γ ⟹ (φ ⭤ ψ) :: Δ := by
  apply and_right
  · apply rotate_right_inv
    apply imply_right_cl
    assumption
  · apply rotate_right_inv
    apply imply_right_cl
    assumption

lemma iff_left (hr : Γ ⟹ Δ ++ [φ, ψ]) (hl : Γ ++ [φ, ψ] ⟹ Δ) : (φ ⭤ ψ) :: Γ ⟹ Δ := by
  apply and_left
  suffices (φ ➝ ψ) :: (ψ ➝ φ) :: Γ ⟹ Δ from weakening this
  apply imply_left
  · apply imply_left
    · exact weakening hr
    · suffices (φ :: Γ) ⟹ φ :: Δ from weakening this
      apply deductInv!
      apply right_Disj!_intro _ (by simp)
  · suffices (ψ ➝ φ) :: ψ :: Γ ⟹ Δ from weakening this
    apply imply_left
    · suffices (ψ :: Γ) ⟹ ψ :: Δ from weakening this
      apply deductInv!
      apply right_Disj!_intro _ (by simp)
    · exact weakening hl

end TwoSided

variable (F)

structure Tableaux.Sequent where
  antecedent : List F
  succedent : List F

abbrev Tableaux := List (Tableaux.Sequent F)

variable {F} (𝓢)

inductive Tableaux.Valid : Tableaux F → Prop where
  | head {Γ Δ τ} : Γ ⟹ Δ → Valid (⟨Γ, Δ⟩ :: τ)
  | tail {S τ} : Valid τ → Valid (S :: τ)

variable {𝓢}

namespace Tableaux.Valid

variable {T U V : Tableaux F} {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ξ Ξ₁ Ξ₂ Λ Λ₁ Λ₂ : List F} {φ ψ χ : F}

local notation:0 Γ:45 " ⟶ " Δ:46 => Tableaux.Sequent.mk Γ Δ

omit [DecidableEq F] [Entailment.Int 𝓢]

@[simp] lemma not_nil : ¬Valid 𝓢 [] := by rintro ⟨⟩

lemma of_mem (H : Γ ⟹ Δ) (h : (Γ ⟶ Δ) ∈ τ) : Valid 𝓢 τ := by
  match τ with
  |           [] => simp_all
  | (Ξ ⟶ Λ) :: τ =>
    rcases show Γ = Ξ ∧ Δ = Λ ∨ (Γ ⟶ Δ) ∈ τ by simpa using h with (⟨rfl, rfl⟩ | h)
    · exact Valid.head H
    · exact (Valid.of_mem H h).tail

lemma of_subset (h : Valid 𝓢 σ) (ss : σ ⊆ τ := by simp) : Valid 𝓢 τ := by
  match σ with
  |           [] => simp_all
  | (Γ ⟶ Δ) :: ε =>
    have ss : (Γ ⟶ Δ) ∈ τ ∧ ε ⊆ τ := by simpa using ss
    rcases h with (h | h)
    · exact Valid.of_mem h ss.1
    · exact h.of_subset ss.2

lemma of_single_uppercedent (H : (Γ ⟹ Δ) → (Ξ ⟹ Λ)) (h : Valid 𝓢 ((Γ ⟶ Δ) :: T)) :
    Valid 𝓢 ((Ξ ⟶ Λ) :: T) := by
  have h : Valid 𝓢 ((Γ ⟶ Δ) :: T) := h.of_subset
  rcases h with (h | h)
  · exact Valid.head (H h)
  · exact h.tail

lemma of_double_uppercedent (H : (Γ₁ ⟹ Δ₁) → (Γ₂ ⟹ Δ₂) → (Ξ ⟹ Λ))
    (h₁ : Valid 𝓢 ((Γ₁ ⟶ Δ₁) :: T)) (h₂ : Valid 𝓢 ((Γ₂ ⟶ Δ₂) :: T)) :
    Valid 𝓢 ((Ξ ⟶ Λ) :: T) := by
  have h₁ : Valid 𝓢 ((Γ₁ ⟶ Δ₁) :: T) := h₁.of_subset
  have h₂ : Valid 𝓢 ((Γ₂ ⟶ Δ₂) :: T) := h₂.of_subset
  rcases h₁ with (h₁ | h₁)
  · rcases h₂ with (h₂ | h₂)
    · exact Valid.head (H h₁ h₂)
    · exact h₂.tail
  · exact h₁.tail

lemma remove : Valid 𝓢 T → Valid 𝓢 ((Γ ⟶ Δ) :: T) :=
  of_subset

variable [DecidableEq F] [Entailment.Int 𝓢]

lemma to_provable (h : Valid 𝓢 [[] ⟶ [φ]]) : 𝓢 ⊢ φ := by
  rcases h
  · exact TwoSided.to_provable <| by assumption
  · simp_all

lemma right_closed (h : φ ∈ Γ) : Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := head <| TwoSided.right_closed h

lemma left_closed (h : φ ∈ Δ) : Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := head <| TwoSided.left_closed h

lemma remove_right : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) :=
  of_single_uppercedent TwoSided.remove_right

lemma remove_left : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  of_single_uppercedent TwoSided.remove_left

lemma rotate_right : Valid 𝓢 ((Γ ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) :=
  of_single_uppercedent TwoSided.rotate_right

lemma rotate_left : Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  of_single_uppercedent TwoSided.rotate_left

lemma verum_right : Valid 𝓢 ((Γ ⟶ ⊤ :: Δ) :: T) :=
  Valid.head TwoSided.verum_right

omit [DecidableEq F] in
lemma falsum_left : Valid 𝓢 ((⊥ :: Γ ⟶ Δ) :: T) :=
  Valid.head TwoSided.falsum_left

lemma falsum_right : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ ⊥ :: Δ) :: T) :=
  of_single_uppercedent TwoSided.falsum_right

lemma verum_left : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((⊤ :: Γ ⟶ Δ) :: T) :=
  of_single_uppercedent TwoSided.verum_left

lemma and_right :
    Valid 𝓢 ((Γ ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ⟶ Δ ++ [ψ]) :: T) → Valid 𝓢 ((Γ ⟶ φ ⋏ ψ :: Δ) :: T) :=
  of_double_uppercedent TwoSided.and_right

lemma or_left :
    Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋎ ψ :: Γ ⟶ Δ) :: T) :=
  of_double_uppercedent TwoSided.or_left

lemma or_right :
    Valid 𝓢 ((Γ ⟶ Δ ++ [φ, ψ]) :: T) → Valid 𝓢 ((Γ ⟶ φ ⋎ ψ :: Δ) :: T) :=
  of_single_uppercedent TwoSided.or_right

lemma and_left :
    Valid 𝓢 ((Γ ++ [φ, ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋏ ψ :: Γ ⟶ Δ) :: T) :=
  of_single_uppercedent TwoSided.and_left

lemma neg_right :
    Valid 𝓢 ((Γ ++ [φ] ⟶ []) :: (Γ ⟶ Δ ++ [∼φ]) :: T) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := fun h ↦ by
  rcases h with (h | h)
  · exact Valid.head <| TwoSided.neg_right_int h
  · rcases h with (h | h)
    · apply head
      exact TwoSided.weakening h
    · exact h.tail

lemma neg_right' :
    Valid 𝓢 ((Γ ++ [φ] ⟶ []) :: (Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := fun h ↦ by
  rcases h with (h | h)
  · exact Valid.head <| TwoSided.neg_right_int h
  · rcases h with (h | h)
    · apply head
      exact TwoSided.weakening h
    · exact h.tail

lemma neg_left :
    Valid 𝓢 ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((∼φ :: Γ ⟶ Δ) :: T) :=
  of_single_uppercedent TwoSided.neg_left_int

lemma imply_right :
    Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ ++ [φ ➝ ψ]) :: T) → Valid 𝓢 ((Γ ⟶ (φ ➝ ψ) :: Δ) :: T) := fun h ↦ by
  have h : Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ ++ [φ ➝ ψ]) :: T) := h.of_subset
  rcases h with (h | h)
  · exact Valid.head <| TwoSided.imply_right_int h
  · rcases h with (h | h)
    · apply head
      exact TwoSided.weakening h
    · exact h.tail

lemma imply_right' :
    Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ (φ ➝ ψ) :: Δ) :: T) := fun h ↦ by
  have h : Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ) :: T) := h.of_subset
  rcases h with (h | h)
  · exact Valid.head <| TwoSided.imply_right_int h
  · rcases h with (h | h)
    · apply head
      exact TwoSided.weakening h
    · exact h.tail

lemma imply_left :
    Valid 𝓢 ((Γ ++ [φ ➝ ψ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 (((φ ➝ ψ) :: Γ ⟶ Δ) :: T) :=
  of_double_uppercedent TwoSided.imply_left_int

end Tableaux.Valid

end LO.Entailment

end
