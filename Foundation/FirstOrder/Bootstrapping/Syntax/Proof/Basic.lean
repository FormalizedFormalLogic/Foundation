module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory

/-! # Internal $\mathbf{LK}$ -/

@[expose] public section
namespace LO

open FirstOrder Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FirstOrder.Arithmetic.Bootstrapping

/-! ## Sequent -/

variable (L)

def IsFormulaSet (s : V) : Prop := ∀ p ∈ s, IsFormula L p

noncomputable def isFormulaSet : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “s. ∀ p ∈' s, !(isSemiformula L).sigma 0 p”)
  (.mkPi “s. ∀ p ∈' s, !(isSemiformula L).pi 0 p”)

variable {L}

namespace IsFormulaSet

section

instance defined : 𝚫₁-Predicate[V] IsFormulaSet L via isFormulaSet L := .mk
  ⟨by intro v; simp [isFormulaSet], by intro v; simp [isFormulaSet]; rfl⟩

instance definable : 𝚫₁-Predicate[V] IsFormulaSet L := defined.to_definable

instance definable' : Γ-[m + 1]-Predicate[V] IsFormulaSet L := .of_deltaOne definable

end

@[simp] lemma empty : IsFormulaSet L (∅ : V) := fun p ↦ by simp

@[simp] lemma singleton {p : V} : IsFormulaSet L ({p} : V) ↔ IsFormula L p := by
  constructor
  · intro h; exact h p (by simp)
  · intro h p; simp only [mem_singleton_iff]
    rintro rfl; exact h

@[simp] lemma insert_iff {p s : V} : IsFormulaSet L (insert p s) ↔ IsFormula L p ∧ IsFormulaSet L s := by
  constructor
  · intro h; exact ⟨h p (by simp), fun q hq ↦ h q (by simp [hq])⟩
  · rintro ⟨hp, hs⟩ q; simp only [mem_bitInsert_iff]; rintro (rfl | hqs)
    · exact hp
    · exact hs q hqs

alias ⟨insert, _⟩ := insert_iff

@[simp] lemma union {s₁ s₂ : V} : IsFormulaSet L (s₁ ∪ s₂) ↔ IsFormulaSet L s₁ ∧ IsFormulaSet L s₂ :=
  ⟨fun h ↦ ⟨fun p hp ↦ h p (by simp [hp]), fun p hp ↦ h p (by simp [hp])⟩,
   fun h p hp ↦ by
    rcases mem_cup_iff.mp hp with (h₁ | h₂)
    · exact h.1 p h₁
    · exact h.2 p h₂⟩

end IsFormulaSet

/-! ### setShift: shift over a sequent -/

variable (L)

noncomputable def setShift : V → V := hfsImage (shift L)

noncomputable def setShiftGraph : 𝚺₁.Semisentence 2 := hfsImage.graph (shiftGraph L)

instance setShift.defined : 𝚺₁-Function₁[V] setShift L via setShiftGraph L := hfsImage.defined _ (shiftGraph L)

instance setShift.definable : 𝚺₁-Function₁[V] setShift L := hfsImage.definable _ (shiftGraph L)

variable {L}
section setShift

lemma mem_setShift_iff {s y : V} : y ∈ setShift L s ↔ ∃ x ∈ s, y = shift L x := mem_hfsImage_iff

@[simp] lemma mem_setShift_union {s t : V} : setShift L (s ∪ t) = setShift L s ∪ setShift L t := mem_hfsImage_union

@[simp] lemma mem_setShift_insert {x s : V} : setShift L (insert x s) = insert (shift L x) (setShift L s) := mem_hfsImage_insert

@[simp] lemma setShift_empty : setShift L (∅ : V) = ∅ := hfsImage_empty

lemma IsFormulaSet.setShift {s : V} (h : IsFormulaSet L s) : IsFormulaSet L (setShift L s) := by
  simp only [IsFormulaSet, mem_setShift_iff, forall_exists_index, and_imp]
  rintro _ p hp rfl; exact (h p hp).shift

lemma shift_mem_setShift {p s : V} (h : p ∈ s) : shift L p ∈ setShift L s := app_mem_hfsImage h

@[simp] lemma IsFormulaSet.setShift_iff {s : V} :
    IsFormulaSet L (Bootstrapping.setShift L s) ↔ IsFormulaSet L s :=
  ⟨by intro h p hp; simpa using h (shift L p) (shift_mem_setShift hp), IsFormulaSet.setShift⟩

end setShift

/-! ### setNeg: negation over a sequent -/

variable (L)

noncomputable def setNeg : V → V := hfsImage (neg L)

noncomputable def setNegGraph : 𝚺₁.Semisentence 2 := hfsImage.graph (negGraph L)

instance setNeg.defined : 𝚺₁-Function₁[V] setNeg L via setNegGraph L := hfsImage.defined _ (negGraph L)

instance setNeg.definable : 𝚺₁-Function₁[V] setNeg L := hfsImage.definable _ (negGraph L)

variable {L}

section setNeg

lemma mem_setNeg_iff {s y : V} : y ∈ setNeg L s ↔ ∃ x ∈ s, y = neg L x := mem_hfsImage_iff

@[simp] lemma mem_setNeg_union {s t : V} : setNeg L (s ∪ t) = setNeg L s ∪ setNeg L t := mem_hfsImage_union

@[simp] lemma mem_setNeg_insert {x s : V} : setNeg L (insert x s) = insert (neg L x) (setNeg L s) := mem_hfsImage_insert

@[simp] lemma setNeg_empty : setNeg L (∅ : V) = ∅ := hfsImage_empty

lemma IsFormulaSet.setNeg {s : V} (h : IsFormulaSet L s) : IsFormulaSet L (setNeg L s) := by
  simp only [IsFormulaSet, mem_setNeg_iff, forall_exists_index, and_imp]
  rintro _ p hp rfl; exact (h p hp).neg

lemma neg_mem_setNeg {p s : V} (h : p ∈ s) : neg L p ∈ setNeg L s := app_mem_hfsImage h

lemma setNeg_subset_of_subset {s t : V} (h : s ⊆ t) : setNeg L s ⊆ setNeg L t :=
  hfsImage_subset_of_subset h

@[simp] lemma IsFormulaSet.setNeg_iff {s : V} :
    IsFormulaSet L (Bootstrapping.setNeg L s) ↔ IsFormulaSet L s :=
  ⟨by intro h p hp; simpa using h (neg L p) (neg_mem_setNeg hp), IsFormulaSet.setNeg⟩

end setNeg

/-- ### Coding of rules -/

noncomputable def identity (s p : V) : V := ⟪s, 0, p⟫ + 1

noncomputable def cutRule (s p d₁ d₂ : V) : V := ⟪s, 8, p, d₁, d₂⟫ + 1

noncomputable def contraction (s d : V) : V := ⟪s, 6, d⟫ + 1

noncomputable def shiftRule (s d : V) : V := ⟪s, 7, d⟫ + 1

noncomputable def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

noncomputable def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

noncomputable def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

noncomputable def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

noncomputable def exsIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

section

def identityGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 0 p ∧ y = y' + 1”

instance identity.defined : 𝚺₀-Function₂[V] identity via identityGraph := .mk fun v ↦ by simp_all [identityGraph, identity]

def verumIntroGraph : 𝚺₀.Semisentence 2 :=
  .mkSigma “y s. ∃ y' < y, !pair₃Def y' s 1 0 ∧ y = y' + 1”

instance verumIntro.defined : 𝚺₀-Function₁[V] verumIntro via verumIntroGraph := .mk fun v ↦ by simp_all [verumIntroGraph, verumIntro]

def andIntroGraph : 𝚺₀.Semisentence 6 :=
  .mkSigma “y s p q dp dq. ∃ y' < y, !pair₆Def y' s 2 p q dp dq ∧ y = y' + 1”

instance andIntro.defined : 𝚺₀-Function₅ (andIntro : V → V → V → V → V → V) via andIntroGraph := .mk fun v ↦ by simp_all [andIntroGraph, andIntro]

def orIntroGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p q d. ∃ y' < y, !pair₅Def y' s 3 p q d ∧ y = y' + 1”

instance orIntro.defined : 𝚺₀-Function₄ (orIntro : V → V → V → V → V) via orIntroGraph := .mk fun v ↦ by simp_all [orIntroGraph, orIntro]

def allIntroGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p d. ∃ y' < y, !pair₄Def y' s 4 p d ∧ y = y' + 1”

instance allIntro.defined : 𝚺₀-Function₃ (allIntro : V → V → V → V) via allIntroGraph := .mk fun v ↦ by simp_all [allIntroGraph, allIntro]

def exsIntroGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p t d. ∃ y' < y, !pair₅Def y' s 5 p t d ∧ y = y' + 1”

instance exsIntro.defined : 𝚺₀-Function₄ (exsIntro : V → V → V → V → V) via exsIntroGraph := .mk fun v ↦ by simp_all [exsIntroGraph, numeral_eq_natCast, exsIntro]

def contractionGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 6 d ∧ y = y' + 1”

instance contraction.defined : 𝚺₀-Function₂ (contraction : V → V → V) via contractionGraph := .mk fun v ↦ by simp_all [contractionGraph, numeral_eq_natCast, contraction]

def shiftRuleGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 7 d ∧ y = y' + 1”

instance shiftRule.defined : 𝚺₀-Function₂ (shiftRule : V → V → V) via shiftRuleGraph := .mk fun v ↦ by simp_all [shiftRuleGraph, numeral_eq_natCast, shiftRule]

def cutRuleGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p d₁ d₂. ∃ y' < y, !pair₅Def y' s 8 p d₁ d₂ ∧ y = y' + 1”

instance cutRule_defined : 𝚺₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleGraph := .mk fun v ↦ by simp_all [cutRuleGraph, numeral_eq_natCast, cutRule]

@[simp] lemma seq_lt_identity (s p : V) : s < identity s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_identity (s p : V) : p < identity s p :=
  le_iff_lt_succ.mp <| le_trans (by simp) <| le_pair_right _ _

@[simp] lemma seq_lt_verumIntro (s : V) : s < verumIntro s := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma seq_lt_andIntro (s p q dp dq : V) : s < andIntro s p q dp dq := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_andIntro (s p q dp dq : V) : p < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma q_lt_andIntro (s p q dp dq : V) : q < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma dp_lt_andIntro (s p q dp dq : V) : dp < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma dq_lt_andIntro (s p q dp dq : V) : dq < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_orIntro (s p q d : V) : s < orIntro s p q d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_orIntro (s p q d : V) : p < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma q_lt_orIntro (s p q d : V) : q < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d_lt_orIntro (s p q d : V) : d < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_allIntro (s p d : V) : s < allIntro s p d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_allIntro (s p d : V) : p < allIntro s p d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma s_lt_allIntro (s p d : V) : d < allIntro s p d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (by simp) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_exsIntro (s p t d : V) : s < exsIntro s p t d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_exsIntro (s p t d : V) : p < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma t_lt_exsIntro (s p t d : V) : t < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d_lt_exsIntro (s p t d : V) : d < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_contraction (s d : V) : s < contraction s d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_contraction (s d : V) : d < contraction s d := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_shiftRule (s d : V) : s < shiftRule s d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_shiftRule (s d : V) : d < shiftRule s d := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_cutRule (s p d₁ d₂ : V) : s < cutRule s p d₁ d₂ := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_cutRule (s p d₁ d₂ : V) : p < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₁_lt_cutRule (s p d₁ d₂ : V) : d₁ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₂_lt_cutRule (s p d₁ d₂ : V) : d₂ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_identity (s p : V) : fstIdx (identity s p) = s := by simp [fstIdx, identity]
@[simp] lemma fstIdx_verumIntro (s : V) : fstIdx (verumIntro s) = s := by simp [fstIdx, verumIntro]
@[simp] lemma fstIdx_andIntro (s p q dp dq : V) : fstIdx (andIntro s p q dp dq) = s := by simp [fstIdx, andIntro]
@[simp] lemma fstIdx_orIntro (s p q dpq : V) : fstIdx (orIntro s p q dpq) = s := by simp [fstIdx, orIntro]
@[simp] lemma fstIdx_allIntro (s p d : V) : fstIdx (allIntro s p d) = s := by simp [fstIdx, allIntro]
@[simp] lemma fstIdx_exsIntro (s p t d : V) : fstIdx (exsIntro s p t d) = s := by simp [fstIdx, exsIntro]
@[simp] lemma fstIdx_contraction (s d : V) : fstIdx (contraction s d) = s := by simp [fstIdx, contraction]
@[simp] lemma fstIdx_shiftRule (s d : V) : fstIdx (shiftRule s d) = s := by simp [fstIdx, shiftRule]
@[simp] lemma fstIdx_cutRule (s p d₁ d₂ : V) : fstIdx (cutRule s p d₁ d₂) = s := by simp [fstIdx, cutRule]

end

/-! ## Internal isDerivation -/

namespace IsDerivation

/-! ### Preparation -/

noncomputable abbrev conseq (x : V) : V := π₁ x

variable (L)

def Phi (C : Set V) (d : V) : Prop :=
  IsFormulaSet L (fstIdx d) ∧
  ( (∃ s p, d = identity s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = contraction s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)))

private lemma phi_iff (C d : V) :
    Phi L {x | x ∈ C} d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = identity s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s < d, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = contraction s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C))) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, p, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨s, p, q, dp, dq, rfl, h⟩ | ⟨s, p, q, dpq, rfl, h⟩ |
      ⟨s, p, dp, rfl, h⟩ | ⟨s, p, t, dp, rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, p, d₁, d₂, rfl, h⟩)
    · left; exact ⟨s, by simp, p, by simp, rfl, h⟩
    · right; left; exact ⟨s, by simp, rfl, h⟩
    · right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · right; right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dpq, by simp, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, by simp, p, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, by simp, p, by simp, t, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, _, p, _, rfl, h⟩ | ⟨s, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dpq, _, rfl, h⟩ |
      ⟨s, _, p, _, dp, _, rfl, h⟩ | ⟨s, _, p, _, t, _, dp, _, rfl, h⟩ | ⟨s, _, d', _, rfl, h⟩ |
      ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, p, _, d₁, _, d₂, _, rfl, h⟩)
    · left; exact ⟨s, p, rfl, h⟩
    · right; left; exact ⟨s, rfl, h⟩
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, h⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, h⟩

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    (∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet L).sigma fst) ∧
    ( (∃ s < d, ∃ p < d, !identityGraph d s p ∧ p ∈ s ∧ ∃ np, !(negGraph L) np p ∧ np ∈ s) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∃ vrm, !qqVerumDef vrm ∧ vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroGraph d s p q dp dq ∧ (∃ and, !qqAndDef and p q ∧ and ∈ s) ∧
          (∃ c, !fstIdxDef c dp ∧ !insertDef c p s ∧ dp ∈ C) ∧
          (∃ c, !fstIdxDef c dq ∧ !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroGraph d s p q dpq ∧ (∃ or, !qqOrDef or p q ∧ or ∈ s) ∧
        ∃ c, !fstIdxDef c dpq ∧ ∃ c', !insertDef c' q s ∧ !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroGraph d s p dp ∧ (∃ all, !qqAllDef all p ∧ all ∈ s) ∧
        ∃ c, !fstIdxDef c dp ∧ ∃ fp, !(freeGraph L) fp p ∧ ∃ ss, !(setShiftGraph L) ss s ∧
        !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exsIntroGraph d s p t dp ∧ (∃ ex, !qqExsDef ex p ∧ ex ∈ s) ∧
        !(isSemiterm L).sigma 0 t ∧ ∃ c, !fstIdxDef c dp ∧ ∃ pt, !(substs1Graph L) pt t p ∧ !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !contractionGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !(setShiftGraph L) s c ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleGraph d s p d₁ d₂ ∧
        (∃ c, !fstIdxDef c d₁ ∧ !insertDef c p s ∧ d₁ ∈ C) ∧
        (∃ c, !fstIdxDef c d₂ ∧ ∃ np, !(negGraph L) np p ∧ !insertDef c np s ∧ d₂ ∈ C)))”
    )
  (.mkPi “d C.
    (∀ fst, !fstIdxDef fst d → !(isFormulaSet L).pi fst) ∧
    ( (∃ s < d, ∃ p < d, !identityGraph d s p ∧ p ∈ s ∧ ∀ np, !(negGraph L) np p → np ∈ s) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∀ vrm, !qqVerumDef vrm → vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroGraph d s p q dp dq ∧ (∀ and, !qqAndDef and p q → and ∈ s) ∧
          (∀ c, !fstIdxDef c dp → !insertDef c p s ∧ dp ∈ C) ∧
          (∀ c, !fstIdxDef c dq → !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroGraph d s p q dpq ∧ (∀ or, !qqOrDef or p q → or ∈ s) ∧
        ∀ c, !fstIdxDef c dpq → ∀ c', !insertDef c' q s → !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroGraph d s p dp ∧ (∀ all, !qqAllDef all p → all ∈ s) ∧
        ∀ c, !fstIdxDef c dp → ∀ fp, !(freeGraph L) fp p → ∀ ss, !(setShiftGraph L) ss s →
          !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exsIntroGraph d s p t dp ∧ (∀ ex, !qqExsDef ex p → ex ∈ s) ∧
        !(isSemiterm L).pi 0 t ∧
        ∀ c, !fstIdxDef c dp → ∀ pt, !(substs1Graph L) pt t p → !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !contractionGraph d s d' ∧ ∀ c, !fstIdxDef c d' → !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∀ c, !fstIdxDef c d' → ∀ ss, !(setShiftGraph L) ss c → s = ss ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleGraph d s p d₁ d₂ ∧
        (∀ c, !fstIdxDef c d₁ → !insertDef c p s ∧ d₁ ∈ C) ∧
        (∀ c, !fstIdxDef c d₂ → ∀ np, !(negGraph L) np p → !insertDef c np s ∧ d₂ ∈ C)))”
    )⟩

lemma Phi_definable : 𝚫₁.Defined (fun v : Fin 2 → V ↦ Phi L {x | x ∈ v 1} (v 0)) (blueprint L).core := .mk <| by
  constructor
  · intro v; simp [blueprint]
  · intro v; simp [phi_iff, blueprint]

def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := Phi_definable _
  monotone := by
    rintro C C' hC _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hC hpC⟩, ⟨hq, hC hqC⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hC hdC⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hC hdC⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hC hdC⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC hd₁C⟩, ⟨h₂, hC hd₂C⟩⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC, by simp⟩, ⟨hq, hqC, by simp⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hdC, by simp⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hdC, by simp⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hdC, by simp⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C, by simp⟩, ⟨h₂, hd₂C, by simp⟩⟩

end IsDerivation

/- ### Main definitions -/

open PeanoMinus ISigma0 ISigma1 Bootstrapping IsDerivation

variable (L)

/-- Internal isDerivation -/
def IsDerivation : V → Prop := (construction L).Fixpoint ![]

/- Internal isDerivation of sequent `s` -/
def IsDerivationOf (d s : V) : Prop := fstIdx d = s ∧ IsDerivation L d

/-- Internal derivability -/
def Derivable (s : V) : Prop := ∃ d, IsDerivationOf L d s

/-- Internal proof -/
@[deprecated IProof]
def IProof (d φ : V) : Prop := IsDerivationOf L d {φ}

/-- Internal provability -/
@[deprecated IProvable]
def IProvable (φ : V) : Prop := ∃ d, IProof L d φ

noncomputable def isDerivation : 𝚫₁.Semisentence 1 := (blueprint L).fixpointDefΔ₁

noncomputable def isDerivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(isDerivation L).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(isDerivation L).pi d”)

noncomputable def derivable : 𝚺₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !(isDerivationOf L).sigma d Γ”

@[deprecated iproof]
noncomputable def iproof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !(isDerivationOf L).sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !(isDerivationOf L).pi d s”)

noncomputable def iprovable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ d, !(iproof L).sigma d φ”

@[deprecated iprovabilityPred]
noncomputable abbrev iprovabilityPred (σ : Sentence L) : Sentence ℒₒᵣ := (iprovable L).val/[⌜σ⌝]

@[deprecated iprovabilityPred']
noncomputable def iprovabilityPred' (σ : Sentence L) : 𝚺₁.Sentence := .mkSigma
  “!(iprovable L) !!(⌜σ⌝)”

@[simp] lemma iprovabilityPred'_val (σ : Sentence L) : (iprovabilityPred' L σ).val = iprovabilityPred L σ := by rfl

variable {L}

section

instance IsDerivation.defined : 𝚫₁-Predicate[V] (IsDerivation L) via isDerivation L := (construction L).fixpoint_definedΔ₁

instance IsDerivation.definable : 𝚫₁-Predicate[V] (IsDerivation L) := IsDerivation.defined.to_definable

instance IsDerivation.definable' : Γ-[m + 1]-Predicate[V] (IsDerivation L) := IsDerivation.definable.of_deltaOne

instance IsDerivationOf.defined : 𝚫₁-Relation[V] (IsDerivationOf L) via isDerivationOf L := .mk
  ⟨by intro v; simp [isDerivationOf], by intro v; simp [isDerivationOf, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance IsDerivationOf.definable : 𝚫₁-Relation[V] IsDerivationOf L := IsDerivationOf.defined.to_definable

instance IsDerivationOf.definable' : Γ-[m + 1]-Relation[V] IsDerivationOf L := IsDerivationOf.definable.of_deltaOne

instance Derivable.defined : 𝚺₁-Predicate[V] (Derivable L) via derivable L := .mk fun v ↦ by simp [Derivable, derivable]

instance Derivable.definable : 𝚺₁-Predicate[V] (Derivable L) := Derivable.defined.to_definable

/-- instance for definability tactic-/
instance Derivable.definable' : 𝚺-[0 + 1]-Predicate[V] (Derivable L) := Derivable.definable

/-

instance Proof.defined : 𝚫₁-Relation[V] T.Proof via T.proof := .mk
  ⟨by intro v; simp [Theory.proof], by intro v; simp [Theory.Proof, Theory.proof, singleton_eq_insert, emptyset_def]⟩

instance Proof.definable : 𝚫₁-Relation[V] T.Proof := Proof.defined.to_definable

instance Proof.definable' : Γ-[m + 1]-Relation[V] T.Proof := Proof.definable.of_deltaOne

instance Provable.defined : 𝚺₁-Predicate[V] T.Provable via T.provable := .mk fun v ↦ by simp [Theory.provable, Theory.Provable]

instance Provable.definable : 𝚺₁-Predicate[V] T.Provable := Provable.defined.to_definable

/-- instance for definability tactic-/
instance Provable.definable' : 𝚺-[0 + 1]-Predicate[V] T.Provable := Provable.definable

-/

end

/-! ### Induction and recursion of isDerivation -/

namespace IsDerivation

lemma case_iff {d : V} :
    IsDerivation L d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = Bootstrapping.identity s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ IsDerivationOf L dp (insert p s) ∧ IsDerivationOf L dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ IsDerivationOf L dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ IsDerivationOf L dp (insert (free L p) (setShift L s))) ∨
      (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ IsDerivationOf L dp (insert (substs1 L t p) s)) ∨
      (∃ s d', d = contraction s d' ∧ fstIdx d' ⊆ s ∧ IsDerivation L d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ IsDerivation L d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ IsDerivationOf L d₁ (insert p s) ∧ IsDerivationOf L d₂ (insert (neg L p) s)) ) :=
  (construction L).case

alias ⟨case, _root_.LO.FirstOrder.Theory.IsDerivation.mk⟩ := case_iff

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    {d} (hd : IsDerivation L d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (identity s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s → IsDerivationOf L dp (insert p s) → IsDerivationOf L dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, IsFormulaSet L s → ∀ p q d, p ^⋎ q ∈ s → IsDerivationOf L d (insert p (insert q s)) →
      P d → P (orIntro s p q d))
    (hAll : ∀ s, IsFormulaSet L s → ∀ p d, ^∀ p ∈ s → IsDerivationOf L d (insert (free L p) (setShift L s)) →
      P d → P (allIntro s p d))
    (hExs : ∀ s, IsFormulaSet L s → ∀ p t d, ^∃ p ∈ s → IsTerm L t → IsDerivationOf L d (insert (substs1 L t p) s) →
      P d → P (exsIntro s p t d))
    (hWk : ∀ s, IsFormulaSet L s → ∀ d, fstIdx d ⊆ s → IsDerivation L d →
      P d → P (contraction s d))
    (hShift : ∀ s, IsFormulaSet L s → ∀ d, s = setShift L (fstIdx d) → IsDerivation L d →
      P d → P (shiftRule s d))
    (hCut : ∀ s, IsFormulaSet L s → ∀ p d₁ d₂, IsDerivationOf L d₁ (insert p s) → IsDerivationOf L d₂ (insert (neg L p) s) →
      P d₁ → P d₂ → P (cutRule s p d₁ d₂)) : P d :=
  (construction L).induction (v := ![]) hP (by
    intro C ih d hd
    rcases hd with ⟨hds,
      (⟨s, p, rfl, hps, hnps⟩ | ⟨s, rfl, hs⟩ |
        ⟨s, p, q, dp, dq, rfl, hpq, h₁, h₂⟩ | ⟨s, p, q, d, rfl, hpq, h⟩ |
        ⟨s, p, d, rfl, hp, h, hC⟩ | ⟨s, p, t, d, rfl, hp, ht, h, hC⟩ |
        ⟨s, d, rfl, h, hC⟩ | ⟨s, d, rfl, h, hC⟩ |
        ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC₁⟩, ⟨h₂, hC₂⟩⟩)⟩
    · exact hAxL s (by simpa using hds) p hps hnps
    · exact hVerumIntro s (by simpa using hds) hs
    · exact hAnd s (by simpa using hds) p q dp dq hpq ⟨h₁.1, (ih dp h₁.2).1⟩ ⟨h₂.1, (ih dq h₂.2).1⟩ (ih dp h₁.2).2 (ih dq h₂.2).2
    · exact hOr s (by simpa using hds) p q d hpq ⟨h.1, (ih d h.2).1⟩ (ih d h.2).2
    · exact hAll s (by simpa using hds) p d hp ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hExs s (by simpa using hds) p t d hp ht ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hWk s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hShift s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hCut s (by simpa using hds) p d₁ d₂ ⟨h₁, (ih d₁ hC₁).1⟩ ⟨h₂, (ih d₂ hC₂).1⟩ (ih d₁ hC₁).2 (ih d₂ hC₂).2)
  d hd

lemma isFormulaSet {d : V} (h : IsDerivation L d) : IsFormulaSet L (fstIdx d) := (h : IsDerivation L d).case.1

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.IsDerivationOf.isFormulaSet {d s : V} (h : IsDerivationOf L d s) : IsFormulaSet L s := by
  simpa [h.1] using h.2.case.1

lemma identity {s p : V} (hs : IsFormulaSet L s) (h : p ∈ s) (hn : neg L p ∈ s) : IsDerivation L (identity s p) :=
  Theory.IsDerivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

lemma verumIntro {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    IsDerivation L (verumIntro s) :=
  Theory.IsDerivation.mk ⟨by simpa using hs, Or.inr <| Or.inl ⟨s, rfl, h⟩⟩

lemma andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : IsDerivationOf L dp (insert p s)) (hdq : IsDerivationOf L dq (insert q s)) :
    IsDerivation L (andIntro s p q dp dq) :=
  Theory.IsDerivation.mk ⟨by simp only [fstIdx_andIntro]; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

lemma orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : IsDerivationOf L dpq (insert p (insert q s))) :
    IsDerivation L (orIntro s p q dpq) :=
  Theory.IsDerivation.mk ⟨by simp only [fstIdx_orIntro]; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

lemma allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : IsDerivationOf L dp (insert (free L p) (setShift L s))) :
    IsDerivation L (allIntro s p dp) :=
  Theory.IsDerivation.mk
    ⟨by simp only [fstIdx_allIntro]; intro q hq; simpa using hdp.isFormulaSet (shift L q) (by simp [shift_mem_setShift hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, dp, rfl, h, hdp⟩⟩

lemma exsIntro {s p t dp : V}
    (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hdp : IsDerivationOf L dp (insert (substs1 L t p) s)) :
    IsDerivation L (exsIntro s p t dp) :=
  Theory.IsDerivation.mk
    ⟨by simp only [fstIdx_exsIntro]; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

lemma contraction {s s' d : V} (hs : IsFormulaSet L s)
    (h : s' ⊆ s) (hd : IsDerivationOf L d s') : IsDerivation L (contraction s d) :=
  Theory.IsDerivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

lemma shiftRule {s d : V}
    (hd : IsDerivationOf L d s) : IsDerivation L (shiftRule (setShift L s) d) :=
  Theory.IsDerivation.mk
    ⟨by simp [hd.isFormulaSet],
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨setShift L s, d, rfl, by simp [hd.1], hd.2⟩⟩

lemma cutRule {s p d₁ d₂ : V}
    (hd₁ : IsDerivationOf L d₁ (insert p s))
    (hd₂ : IsDerivationOf L d₂ (insert (neg L p) s)) :
    IsDerivation L (cutRule s p d₁ d₂) :=
  Theory.IsDerivation.mk
    ⟨by simp only [fstIdx_cutRule]; intro q hq; exact hd₁.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩⟩

end IsDerivation

namespace Derivable

lemma isFormulaSet {s : V} (h : Derivable L s) : IsFormulaSet L s := by
  rcases h with ⟨d, hd⟩; exact hd.isFormulaSet

lemma em {s : V} (hs : IsFormulaSet L s) (p) (h : p ∈ s) (hn : neg L p ∈ s) :
    Derivable L s := ⟨identity s p, by simp, IsDerivation.identity hs h hn⟩

lemma verum {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    Derivable L s := ⟨verumIntro s, by simp, IsDerivation.verumIntro hs h⟩

lemma and_m {s p q : V} (h : p ^⋏ q ∈ s) (hp : Derivable L (insert p s)) (hq : Derivable L (insert q s)) :
    Derivable L s := by
  rcases hp with ⟨dp, hdp⟩; rcases hq with ⟨dq, hdq⟩
  exact ⟨andIntro s p q dp dq, by simp, IsDerivation.andIntro h hdp hdq⟩

lemma or_m {s p q : V} (h : p ^⋎ q ∈ s) (hpq : Derivable L (insert p (insert q s))) :
    Derivable L s := by
  rcases hpq with ⟨dpq, hdpq⟩
  exact ⟨orIntro s p q dpq, by simp, IsDerivation.orIntro h hdpq⟩

lemma all_m {s p : V} (h : ^∀ p ∈ s) (hp : Derivable L (insert (free L p) (setShift L s))) :
    Derivable L s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨allIntro s p dp, by simp, IsDerivation.allIntro h hdp⟩

lemma ex_m {s p t : V} (h : ^∃ p ∈ s) (ht : IsTerm L t) (hp : Derivable L (insert (substs1 L t p) s)) :
    Derivable L s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨exsIntro s p t dp, by simp, IsDerivation.exsIntro h ht hdp⟩

lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : Derivable L s') :
    Derivable L s := by
  rcases hd with ⟨d, hd⟩
  exact ⟨contraction s d, by simp, IsDerivation.contraction hs h hd⟩

lemma shift {s : V} (hd : Derivable L s) :
    Derivable L (setShift L s) := by
  rcases hd with ⟨d, hd⟩
  exact ⟨shiftRule (setShift L s) d, by simp, IsDerivation.shiftRule hd⟩

lemma ofSetEq {s s' : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : Derivable L s') :
    Derivable L s := by
  have : s' = s := mem_ext h
  rcases this; exact hd

lemma exchange {s p q : V} (h : Derivable L (insert p <| insert q s)) :
    Derivable L (insert q <| insert p s) := h.ofSetEq (fun x ↦ by simp; tauto)

lemma cut {s : V} (p) (hd₁ : Derivable L (insert p s)) (hd₂ : Derivable L (insert (neg L p) s)) :
    Derivable L s := by
  rcases hd₁ with ⟨d₁, hd₁⟩; rcases hd₂ with ⟨d₂, hd₂⟩
  exact ⟨cutRule s p d₁ d₂, by simp, IsDerivation.cutRule hd₁ hd₂⟩

lemma and {s p q : V} (hp : Derivable L (insert p s)) (hq : Derivable L (insert q s)) :
    Derivable L (insert (p ^⋏ q) s) :=
  and_m (p := p) (q := q) (by simp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hq)

lemma or {s p q : V} (hpq : Derivable L (insert p (insert q s))) :
    Derivable L (insert (p ^⋎ q) s) :=
  or_m (p := p) (q := q) (by simp)
    (wk (by simp [hpq.isFormulaSet.insert, hpq.isFormulaSet.insert.2.insert])
      (insert_subset_insert_of_subset _ <| insert_subset_insert_of_subset _ <| by simp) hpq)

/-- Crucial inducion for formalized $\Sigma_1$-completeness. -/
lemma conj (ps : V) {s : V} (hs : IsFormulaSet L s)
    (ds : ∀ i < len ps, Derivable L (insert ps.[i] s)) : Derivable L (insert (^⋀ ps) s) := by
  have : ∀ k ≤ len ps, Derivable L (insert (^⋀ (takeLast ps k)) s) := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa using verum (by simp [hs]) (by simp)
    case succ k ih =>
      have ih : Derivable L (insert (^⋀ takeLast ps k) s) := ih (le_trans le_self_add hk)
      have : Derivable L (insert ps.[len ps - (k + 1)] s) := ds (len ps - (k + 1)) ((tsub_lt_iff_left hk).mpr (by simp))
      simpa [takeLast_succ_of_lt (succ_le_iff_lt.mp hk)] using this.and ih
  simpa using this (len ps) (by rfl)

lemma disjDistr (ps s : V) (d : Derivable L (vecToSet ps ∪ s)) : Derivable L (insert (^⋁ ps) s) := by
  have : ∀ k ≤ len ps, ∀ s' ≤ vecToSet ps, s' ⊆ vecToSet ps →
      (∀ i < len ps - k, ps.[i] ∈ s') → Derivable L (insert (^⋁ takeLast ps k) (s' ∪ s)) := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · apply HierarchySymbol.Definable.imp (by definability)
      apply HierarchySymbol.Definable.ball_le (by definability)
      apply HierarchySymbol.Definable.imp (by definability)
      apply HierarchySymbol.Definable.imp (by definability)
      definability
    case zero =>
      intro s' _ ss hs'
      refine wk ?_ ?_ d
      · suffices IsFormulaSet L s' by simpa [by simpa using d.isFormulaSet]
        intro x hx
        exact d.isFormulaSet x (by simp [ss hx])
      · intro x
        simp only [mem_cup_iff, mem_vecToSet_iff, takeLast_zero, qqDisj_nil, mem_bitInsert_iff]
        rintro (⟨i, hi, rfl⟩ | hx)
        · right; left; exact hs' i (by simpa using hi)
        · right; right; exact hx
    case succ k ih =>
      intro s' _ ss hs'
      simp only [takeLast_succ_of_lt (succ_le_iff_lt.mp hk), qqDisj_cons]
      apply Derivable.or
      let s'' := insert ps.[len ps - (k + 1)] s'
      have hs'' : s'' ⊆ vecToSet ps := by
        intro x; simp only [mem_bitInsert_iff, s'']
        rintro (rfl | h)
        · exact mem_vecToSet_iff.mpr ⟨_, by simp [tsub_lt_iff_left hk], rfl⟩
        · exact ss h
      have : Derivable L (insert (^⋁ takeLast ps k) (s'' ∪ s)) := by
        refine ih (le_trans (by simp) hk) s'' (le_of_subset hs'') hs'' ?_
        intro i hi
        have : i ≤ len ps - (k + 1) := by
          simpa [Arithmetic.sub_sub] using le_sub_one_of_lt hi
        rcases lt_or_eq_of_le this with (hi | rfl)
        · simp [s'', hs' i hi]
        · simp [s'']
      exact ofSetEq (by intro x; simp [s'']; tauto) this
  simpa using this (len ps) (by rfl) ∅ (by simp [emptyset_def]) (by simp) (by simp)

lemma disj (ps s : V) {i} (hps : ∀ i < len ps, IsFormula L ps.[i])
  (hi : i < len ps) (d : Derivable L (insert ps.[i] s)) : Derivable L (insert (^⋁ ps) s) :=
  disjDistr ps s <| wk
    (by suffices IsFormulaSet L (vecToSet ps) by simpa [by simpa using d.isFormulaSet]
        intro x hx; rcases mem_vecToSet_iff.mp hx with ⟨i, hi, rfl⟩; exact hps i hi)
    (by
      intro x; simp only [mem_bitInsert_iff, mem_cup_iff]
      rintro (rfl | hx)
      · left; exact mem_vecToSet_iff.mpr ⟨i, hi, rfl⟩
      · right; exact hx) d

lemma all {p s : V} (hp : IsSemiformula L 1 p) (dp : Derivable L (insert (free L p) (setShift L s))) : Derivable L (insert (^∀ p) s) :=
  all_m (p := p) (by simp) (wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp)

lemma exs {p t s : V} (hp : IsSemiformula L 1 p) (ht : IsTerm L t)
    (dp : Derivable L (insert (substs1 L t p) s)) : Derivable L (insert (^∃ p) s) :=
  ex_m (p := p) (by simp) ht <| wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp

end Derivable

/-! ## Proof with axiom -/

variable (T : Theory L) [T.Δ₁]

def IsProof (d φ : V) : Prop := (∀ x ∈ pi₁ d, x ∈ T.Δ₁Class) ∧ IsDerivationOf L (pi₂ d) (insert φ (setNeg L (pi₁ d)))

def Provable (φ : V) : Prop := ∃ d, IsProof T d φ

variable {T}

lemma provable_iff_derivable {φ : V} : Provable T φ ↔ ∃ s : V, (∀ x ∈ s, x ∈ T.Δ₁Class) ∧ Derivable L (insert φ (setNeg L s)) := by
  constructor
  · rintro ⟨d, hT, hd⟩
    exact ⟨pi₁ d, hT, pi₂ d, hd⟩
  · rintro ⟨s, hT, d, hd⟩
    exact ⟨⟪s, d⟫, by simpa [IsProof] using And.intro hT hd⟩


alias ⟨Provable.toDerivable, Derivable.toProvable⟩ := provable_iff_derivable

variable (T)

noncomputable def isProof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “p φ.
    ∃ s d, !pairDef p s d ∧ (∀ x ∈' s, !T.Δ₁ch.sigma x) ∧
    ∃ ns, !(setNegGraph L) ns s ∧
    ∃ ins, !insertDef ins φ ns ∧ !(isDerivationOf L).sigma d ins”)
  (.mkPi “p φ.
    ∀ s d, !pairDef p s d → (∀ x ∈' s, !T.Δ₁ch.pi x) ∧
    ∀ ns, !(setNegGraph L) ns s →
    ∀ ins, !insertDef ins φ ns → !(isDerivationOf L).pi d ins”)

set_option linter.flexible false in instance IsProof.defined : 𝚫₁-Relation[V] (IsProof T) via isProof T := ⟨fun x ↦ by
  simp [isProof];
  constructor
  · intro ⟨x, y, e, h⟩ x y e2
    simp [e] at e2
    rcases e2 with ⟨rfl, rfl⟩
    simpa
  · intro h
    refine ⟨pi₁ (x 0), pi₂ (x 0), by simp, ?_⟩
    grind,
  .of_vec_two fun x y ↦ by
    simp [isProof]
    constructor
    · rintro ⟨x, y, rfl, h⟩
      simpa [IsProof]
    · rintro h
      refine ⟨pi₁ x, pi₂ x, by simp, by simpa [IsProof]⟩⟩

instance IsProof.definable : 𝚫₁-Relation[V] (IsProof T) := (IsProof.defined T).to_definable

instance IsProof.definable' : Γ-[m + 1]-Relation[V] (IsProof T) := (IsProof.definable T).of_deltaOne

noncomputable def provable : 𝚺₁.Semisentence 1 := .mkSigma “φ. ∃ d, !(isProof T).sigma d φ”

instance Provable.defined : 𝚺₁-Predicate[V] (Provable T) via provable T := .mk fun v ↦ by simp [provable, Provable]

instance Provable.definable : 𝚺₁-Predicate[V] (Provable T) := (Provable.defined T).to_definable

instance Provable.definable' : 𝚺-[0 + 1]-Predicate[V] (Provable T) := Provable.definable T

namespace Provable

lemma exists_common_axiom_set {ps : V} (ds : ∀ i < len ps, Provable T ps.[i]) :
    ∃ s : V, (∀ x ∈ s, x ∈ T.Δ₁Class) ∧ IsFormulaSet L (setNeg L s) ∧
      ∀ i < len ps, Derivable L (insert ps.[i] (setNeg L s)) := by
    have : ∀ i ∈ under (len ps), ∃ s : V, (∀ x ∈ s, x ∈ T.Δ₁Class) ∧ Derivable L (insert ps.[i] (setNeg L s)) := by
      simpa [provable_iff_derivable] using ds
    let ⟨f, hf, fdom, H⟩ := sigmaOne_skolem (by definability) this
    let s := ⋃ʰᶠ range f
    have hs : IsFormulaSet L (setNeg L s) := by
      intro φ hφ
      rcases mem_setNeg_iff.mp hφ with ⟨p, hp, rfl⟩
      have : ∃ s_i, (∃ i, ⟪i, s_i⟫ ∈ f) ∧ p ∈ s_i := by simpa [s, mem_range_iff] using hp
      rcases this with ⟨s_i, ⟨i, hi⟩, hp⟩
      exact (H i s_i hi).2.isFormulaSet (neg L p) (by simp [neg_mem_setNeg hp])
    refine ⟨s, ?_, hs, ?_⟩
    · intro φ hφ
      have : ∃ s_i, (∃ i, ⟪i, s_i⟫ ∈ f) ∧ φ ∈ s_i := by simpa [s, mem_range_iff] using hφ
      rcases this with ⟨s_i, ⟨i, hi⟩, hφ⟩
      exact (H i s_i hi).1 φ hφ
    · intro i hi
      have hidom : i ∈ domain f := by simpa [fdom] using hi
      rcases mem_domain_iff.mp hidom with ⟨s_i, hi⟩
      refine Derivable.wk ?_ ?_ (H i s_i hi).2
      · intro φ hφ
        simp only [mem_bitInsert_iff] at hφ
        rcases hφ with rfl | hφ
        · exact (H i s_i hi).2.isFormulaSet ps.[i] (by simp)
        · exact hs φ hφ
      · intro φ
        simp only [mem_bitInsert_iff]
        rintro (rfl | hφ)
        · simp
        · right
          exact setNeg_subset_of_subset (by intro p hp; exact mem_sUnion_iff.mpr ⟨s_i, mem_range_iff.mpr ⟨i, hi⟩, hp⟩) hφ

lemma conj (ps : V)
    (ds : ∀ i < len ps, Provable T ps.[i]) : Provable T (^⋀ ps) := by
  rcases exists_common_axiom_set (T := T) (ps := ps) ds with ⟨s, hT, hs, hds⟩
  exact Derivable.toProvable ⟨s, hT, Derivable.conj ps hs hds⟩

lemma disj (ps : V) {i} (hps : ∀ i < len ps, IsFormula L ps.[i])
    (hi : i < len ps) (d : Provable T ps.[i]) : Provable T (^⋁ ps) :=
  let ⟨s, hT, d⟩ := d.toDerivable
  Derivable.toProvable ⟨s, hT, Derivable.disj _ _ hps hi d⟩

end Provable

end FirstOrder.Arithmetic.Bootstrapping

end LO
