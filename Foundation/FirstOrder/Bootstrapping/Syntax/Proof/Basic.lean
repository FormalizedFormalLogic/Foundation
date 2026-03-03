module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory

@[expose] public section
namespace LO

open FirstOrder Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

namespace FirstOrder.Arithmetic.Bootstrapping

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

variable (L)

lemma setShift_existsUnique (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = shift L x :=
  sigma₁_replacement (by definability) s

noncomputable def setShift (s : V) : V := Classical.choose! (setShift_existsUnique L s)

noncomputable def setShiftGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t s. (∀ y ∈' t, ∃ x ∈' s, !(shiftGraph L) y x) ∧ (∀ x ∈' s, ∃ y, !(shiftGraph L) y x ∧ y ∈ t)”

variable {L}

section setShift

lemma mem_setShift_iff {s y : V} : y ∈ setShift L s ↔ ∃ x ∈ s, y = shift L x :=
  Classical.choose!_spec (setShift_existsUnique L s) y

lemma IsFormulaSet.setShift {s : V} (h : IsFormulaSet L s) : IsFormulaSet L (setShift L s) := by
  simp only [IsFormulaSet, mem_setShift_iff, forall_exists_index, and_imp]
  rintro _ p hp rfl; exact (h p hp).shift

lemma shift_mem_setShift {p s : V} (h : p ∈ s) : shift L p ∈ setShift L s :=
  mem_setShift_iff.mpr ⟨p, h, rfl⟩

@[simp] lemma IsFormulaSet.setShift_iff {s : V} :
    IsFormulaSet L (Bootstrapping.setShift L s) ↔ IsFormulaSet L s :=
  ⟨by intro h p hp; simpa using h (shift L p) (shift_mem_setShift hp), IsFormulaSet.setShift⟩

@[simp] lemma mem_setShift_union {s t : V} : setShift L (s ∪ t) = setShift L s ∪ setShift L t := mem_ext <| by
  simp only [mem_setShift_iff, mem_cup_iff]; intro x
  constructor
  · rintro ⟨z, (hz | hz), rfl⟩
    · left; exact ⟨z, hz, rfl⟩
    · right; exact ⟨z, hz, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Or.inl hz, rfl⟩
    · exact ⟨z, Or.inr hz, rfl⟩

@[simp] lemma mem_setShift_insert {x s : V} : setShift L (insert x s) = insert (shift L x) (setShift L s) := mem_ext <| by
  simp [mem_setShift_iff]

@[simp] lemma setShift_empty : setShift L (∅ : V) = ∅ := mem_ext <| by simp [mem_setShift_iff]
section

private lemma setShift_graph (t s : V) :
    t = setShift L s ↔ (∀ y ∈ t, ∃ x ∈ s, y = shift L x) ∧ (∀ x ∈ s, shift L x ∈ t) := by
  constructor
  · rintro rfl
    constructor
    · intro y hy; exact mem_setShift_iff.mp hy
    · intro x hx; exact mem_setShift_iff.mpr ⟨x, hx, rfl⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext; intro y; constructor
    · intro hy; exact mem_setShift_iff.mpr (h₁ y hy)
    · intro hy
      rcases mem_setShift_iff.mp hy with ⟨x, hx, rfl⟩
      exact h₂ x hx

instance setShift.defined : 𝚺₁-Function₁[V] setShift L via setShiftGraph L := .mk fun v ↦ by simp [setShiftGraph, setShift_graph]

instance setShift.definable : 𝚺₁-Function₁[V] setShift L := setShift.defined.to_definable

end

end setShift

noncomputable def axL (s p : V) : V := ⟪s, 0, p⟫ + 1

noncomputable def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

noncomputable def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

noncomputable def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

noncomputable def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

noncomputable def exsIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

noncomputable def wkRule (s d : V) : V := ⟪s, 6, d⟫ + 1

noncomputable def shiftRule (s d : V) : V := ⟪s, 7, d⟫ + 1

noncomputable def cutRule (s p d₁ d₂ : V) : V := ⟪s, 8, p, d₁, d₂⟫ + 1

noncomputable def axm (s p : V) : V := ⟪s, 9, p⟫ + 1

section

def axLGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 0 p ∧ y = y' + 1”

instance axL.defined : 𝚺₀-Function₂[V] axL via axLGraph := .mk fun v ↦ by simp_all [axLGraph, axL]

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

def wkRuleGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 6 d ∧ y = y' + 1”

instance wkRule.defined : 𝚺₀-Function₂ (wkRule : V → V → V) via wkRuleGraph := .mk fun v ↦ by simp_all [wkRuleGraph, numeral_eq_natCast, wkRule]

def shiftRuleGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 7 d ∧ y = y' + 1”

instance shiftRule.defined : 𝚺₀-Function₂ (shiftRule : V → V → V) via shiftRuleGraph := .mk fun v ↦ by simp_all [shiftRuleGraph, numeral_eq_natCast, shiftRule]

def cutRuleGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p d₁ d₂. ∃ y' < y, !pair₅Def y' s 8 p d₁ d₂ ∧ y = y' + 1”

instance cutRule_defined : 𝚺₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleGraph := .mk fun v ↦ by simp_all [cutRuleGraph, numeral_eq_natCast, cutRule]

def axmGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 9 p ∧ y = y' + 1”

instance axm_defined : 𝚺₀-Function₂ (axm : V → V → V) via axmGraph := .mk fun v ↦ by simp_all [axmGraph, numeral_eq_natCast, axm]

@[simp] lemma seq_lt_axL (s p : V) : s < axL s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_axL (s p : V) : p < axL s p :=
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

@[simp] lemma seq_lt_wkRule (s d : V) : s < wkRule s d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_wkRule (s d : V) : d < wkRule s d := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_shiftRule (s d : V) : s < shiftRule s d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_shiftRule (s d : V) : d < shiftRule s d := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_cutRule (s p d₁ d₂ : V) : s < cutRule s p d₁ d₂ := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_cutRule (s p d₁ d₂ : V) : p < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₁_lt_cutRule (s p d₁ d₂ : V) : d₁ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₂_lt_cutRule (s p d₁ d₂ : V) : d₂ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_axm (s p : V) : s < axm s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_axm (s p : V) : p < axm s p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_axL (s p : V) : fstIdx (axL s p) = s := by simp [fstIdx, axL]
@[simp] lemma fstIdx_verumIntro (s : V) : fstIdx (verumIntro s) = s := by simp [fstIdx, verumIntro]
@[simp] lemma fstIdx_andIntro (s p q dp dq : V) : fstIdx (andIntro s p q dp dq) = s := by simp [fstIdx, andIntro]
@[simp] lemma fstIdx_orIntro (s p q dpq : V) : fstIdx (orIntro s p q dpq) = s := by simp [fstIdx, orIntro]
@[simp] lemma fstIdx_allIntro (s p d : V) : fstIdx (allIntro s p d) = s := by simp [fstIdx, allIntro]
@[simp] lemma fstIdx_exsIntro (s p t d : V) : fstIdx (exsIntro s p t d) = s := by simp [fstIdx, exsIntro]
@[simp] lemma fstIdx_wkRule (s d : V) : fstIdx (wkRule s d) = s := by simp [fstIdx, wkRule]
@[simp] lemma fstIdx_shiftRule (s d : V) : fstIdx (shiftRule s d) = s := by simp [fstIdx, shiftRule]
@[simp] lemma fstIdx_cutRule (s p d₁ d₂ : V) : fstIdx (cutRule s p d₁ d₂) = s := by simp [fstIdx, cutRule]
@[simp] lemma fstIdx_axm (s p : V) : fstIdx (axm s p) = s := by simp [fstIdx, axm]

end

namespace Derivation

noncomputable abbrev conseq (x : V) : V := π₁ x

variable (T)

def Phi (C : Set V) (d : V) : Prop :=
  IsFormulaSet L (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)) ∨
    (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) )

private lemma phi_iff (C d : V) :
    Phi T {x | x ∈ C} d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
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
        d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, p, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨s, p, q, dp, dq, rfl, h⟩ | ⟨s, p, q, dpq, rfl, h⟩ |
      ⟨s, p, dp, rfl, h⟩ | ⟨s, p, t, dp, rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, p, d₁, d₂, rfl, h⟩ | ⟨s, p, rfl, h⟩)
    · left; exact ⟨s, by simp, p, by simp, rfl, h⟩
    · right; left; exact ⟨s, by simp, rfl, h⟩
    · right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · right; right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dpq, by simp, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, by simp, p, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, by simp, p, by simp, t, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨s, by simp, p, by simp, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, _, p, _, rfl, h⟩ | ⟨s, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dpq, _, rfl, h⟩ |
      ⟨s, _, p, _, dp, _, rfl, h⟩ | ⟨s, _, p, _, t, _, dp, _, rfl, h⟩ | ⟨s, _, d', _, rfl, h⟩ |
      ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, p, _, d₁, _, d₂, _, rfl, h⟩ | ⟨s, _, p, _, h⟩)
    · left; exact ⟨s, p, rfl, h⟩
    · right; left; exact ⟨s, rfl, h⟩
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, h⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨s, p, d₁, d₂, rfl, h⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    (∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet L).sigma fst) ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ p ∈ s ∧ ∃ np, !(negGraph L) np p ∧ np ∈ s) ∨
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
        !wkRuleGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !(setShiftGraph L) s c ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleGraph d s p d₁ d₂ ∧
        (∃ c, !fstIdxDef c d₁ ∧ !insertDef c p s ∧ d₁ ∈ C) ∧
        (∃ c, !fstIdxDef c d₂ ∧ ∃ np, !(negGraph L) np p ∧ !insertDef c np s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        !axmGraph d s p ∧ p ∈ s ∧ !T.Δ₁ch.sigma p) )”
    )
  (.mkPi “d C.
    (∀ fst, !fstIdxDef fst d → !(isFormulaSet L).pi fst) ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ p ∈ s ∧ ∀ np, !(negGraph L) np p → np ∈ s) ∨
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
        !wkRuleGraph d s d' ∧ ∀ c, !fstIdxDef c d' → !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∀ c, !fstIdxDef c d' → ∀ ss, !(setShiftGraph L) ss c → s = ss ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleGraph d s p d₁ d₂ ∧
        (∀ c, !fstIdxDef c d₁ → !insertDef c p s ∧ d₁ ∈ C) ∧
        (∀ c, !fstIdxDef c d₂ → ∀ np, !(negGraph L) np p → !insertDef c np s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        !axmGraph d s p ∧ p ∈ s ∧ !T.Δ₁ch.pi p) )”
    )⟩

lemma Phi_definable : 𝚫₁.Defined (fun v : Fin 2 → V ↦ Phi T {x | x ∈ v 1} (v 0)) (blueprint T).core := .mk <| by
  constructor
  · intro v; simp [blueprint]
  · intro v; simp [phi_iff, blueprint]

def construction : Fixpoint.Construction V (blueprint T) where
  Φ := fun _ ↦ Phi T
  defined := Phi_definable _
  monotone := by
    rintro C C' hC _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩ | ⟨s, p, h⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hC hpC⟩, ⟨hq, hC hqC⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hC hdC⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hC hdC⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hC hdC⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC hd₁C⟩, ⟨h₂, hC hd₂C⟩⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

instance : (construction T).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩ | ⟨s, p, h⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC, by simp⟩, ⟨hq, hqC, by simp⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hdC, by simp⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hdC, by simp⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hdC, by simp⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C, by simp⟩, ⟨h₂, hd₂C, by simp⟩⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

end Derivation

end FirstOrder.Arithmetic.Bootstrapping

namespace FirstOrder.Theory

open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

variable (T)

def Derivation : V → Prop := (construction T).Fixpoint ![]

def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ T.Derivation d

def Derivable (s : V) : Prop := ∃ d, T.DerivationOf d s

def Proof (d φ : V) : Prop := T.DerivationOf d {φ}

def Provable (φ : V) : Prop := ∃ d, T.Proof d φ

noncomputable def derivation : 𝚫₁.Semisentence 1 := (blueprint T).fixpointDefΔ₁

noncomputable def derivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !T.derivation.sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !T.derivation.pi d”)

noncomputable def derivable : 𝚺₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !T.derivationOf.sigma d Γ”

noncomputable def proof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !T.derivationOf.sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !T.derivationOf.pi d s”)

noncomputable def provable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ d, !T.proof.sigma d φ”

noncomputable abbrev provabilityPred (σ : Sentence L) : ArithmeticSentence := T.provable.val/[⌜σ⌝]

noncomputable def provabilityPred' (σ : Sentence L) : 𝚺₁.Sentence := .mkSigma
  “!T.provable !!(⌜σ⌝)”

@[simp] lemma provabilityPred'_val (σ : Sentence L) : (T.provabilityPred' σ).val = T.provabilityPred σ := by rfl

variable {T}

section

instance Derivation.defined : 𝚫₁-Predicate[V] T.Derivation via T.derivation := (construction T).fixpoint_definedΔ₁

instance Derivation.definable : 𝚫₁-Predicate[V] T.Derivation := Derivation.defined.to_definable

instance Derivation.definable' : Γ-[m + 1]-Predicate[V] T.Derivation := Derivation.definable.of_deltaOne

instance DerivationOf.defined : 𝚫₁-Relation[V] T.DerivationOf via T.derivationOf := .mk
  ⟨by intro v; simp [Theory.derivationOf], by intro v; simp [Theory.derivationOf, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance DerivationOf.definable : 𝚫₁-Relation[V] T.DerivationOf := DerivationOf.defined.to_definable

instance DerivationOf.definable' : Γ-[m + 1]-Relation[V] T.DerivationOf := DerivationOf.definable.of_deltaOne

instance Derivable.defined : 𝚺₁-Predicate[V] T.Derivable via T.derivable := .mk fun v ↦ by simp [Theory.derivable, Theory.Derivable]

instance Derivable.definable : 𝚺₁-Predicate[V] T.Derivable := Derivable.defined.to_definable

/-- instance for definability tactic-/
instance Derivable.definable' : 𝚺-[0 + 1]-Predicate[V] T.Derivable := Derivable.definable

instance Proof.defined : 𝚫₁-Relation[V] T.Proof via T.proof := .mk
  ⟨by intro v; simp [Theory.proof], by intro v; simp [Theory.Proof, Theory.proof, singleton_eq_insert, emptyset_def]⟩

instance Proof.definable : 𝚫₁-Relation[V] T.Proof := Proof.defined.to_definable

instance Proof.definable' : Γ-[m + 1]-Relation[V] T.Proof := Proof.definable.of_deltaOne

instance Provable.defined : 𝚺₁-Predicate[V] T.Provable via T.provable := .mk fun v ↦ by simp [Theory.provable, Theory.Provable]

instance Provable.definable : 𝚺₁-Predicate[V] T.Provable := Provable.defined.to_definable

/-- instance for definability tactic-/
instance Provable.definable' : 𝚺-[0 + 1]-Predicate[V] T.Provable := Provable.definable

end

namespace Derivation

lemma case_iff {d : V} :
    T.Derivation d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = Bootstrapping.axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ T.DerivationOf dp (insert p s) ∧ T.DerivationOf dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ T.DerivationOf dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ T.DerivationOf dp (insert (free L p) (setShift L s))) ∨
      (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ T.DerivationOf dp (insert (substs1 L t p) s)) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ T.Derivation d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ T.Derivation d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ T.DerivationOf d₁ (insert p s) ∧ T.DerivationOf d₂ (insert (neg L p) s)) ∨
      (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) :=
  (construction T).case

alias ⟨case, _root_.LO.FirstOrder.Theory.Derivation.mk⟩ := case_iff

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    {d} (hd : T.Derivation d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s → T.DerivationOf dp (insert p s) → T.DerivationOf dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, IsFormulaSet L s → ∀ p q d, p ^⋎ q ∈ s → T.DerivationOf d (insert p (insert q s)) →
      P d → P (orIntro s p q d))
    (hAll : ∀ s, IsFormulaSet L s → ∀ p d, ^∀ p ∈ s → T.DerivationOf d (insert (free L p) (setShift L s)) →
      P d → P (allIntro s p d))
    (hExs : ∀ s, IsFormulaSet L s → ∀ p t d, ^∃ p ∈ s → IsTerm L t → T.DerivationOf d (insert (substs1 L t p) s) →
      P d → P (exsIntro s p t d))
    (hWk : ∀ s, IsFormulaSet L s → ∀ d, fstIdx d ⊆ s → T.Derivation d →
      P d → P (wkRule s d))
    (hShift : ∀ s, IsFormulaSet L s → ∀ d, s = setShift L (fstIdx d) → T.Derivation d →
      P d → P (shiftRule s d))
    (hCut : ∀ s, IsFormulaSet L s → ∀ p d₁ d₂, T.DerivationOf d₁ (insert p s) → T.DerivationOf d₂ (insert (neg L p) s) →
      P d₁ → P d₂ → P (cutRule s p d₁ d₂))
    (hRoot : ∀ s, IsFormulaSet L s → ∀ p, p ∈ s → p ∈ T.Δ₁Class → P (axm s p)) : P d :=
  (construction T).induction (v := ![]) hP (by
    intro C ih d hd
    rcases hd with ⟨hds,
      (⟨s, p, rfl, hps, hnps⟩ | ⟨s, rfl, hs⟩ |
        ⟨s, p, q, dp, dq, rfl, hpq, h₁, h₂⟩ | ⟨s, p, q, d, rfl, hpq, h⟩ |
        ⟨s, p, d, rfl, hp, h, hC⟩ | ⟨s, p, t, d, rfl, hp, ht, h, hC⟩ |
        ⟨s, d, rfl, h, hC⟩ | ⟨s, d, rfl, h, hC⟩ |
        ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC₁⟩, ⟨h₂, hC₂⟩⟩ | ⟨s, p, rfl, hs, hT⟩)⟩
    · exact hAxL s (by simpa using hds) p hps hnps
    · exact hVerumIntro s (by simpa using hds) hs
    · exact hAnd s (by simpa using hds) p q dp dq hpq ⟨h₁.1, (ih dp h₁.2).1⟩ ⟨h₂.1, (ih dq h₂.2).1⟩ (ih dp h₁.2).2 (ih dq h₂.2).2
    · exact hOr s (by simpa using hds) p q d hpq ⟨h.1, (ih d h.2).1⟩ (ih d h.2).2
    · exact hAll s (by simpa using hds) p d hp ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hExs s (by simpa using hds) p t d hp ht ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hWk s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hShift s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hCut s (by simpa using hds) p d₁ d₂ ⟨h₁, (ih d₁ hC₁).1⟩ ⟨h₂, (ih d₂ hC₂).1⟩ (ih d₁ hC₁).2 (ih d₂ hC₂).2
    · exact hRoot s (by simpa using hds) p hs hT) d hd

lemma isFormulaSet {d : V} (h : T.Derivation d) : IsFormulaSet L (fstIdx d) := (h : T.Derivation d).case.1

lemma _root_.LO.FirstOrder.Theory.DerivationOf.isFormulaSet {d s : V} (h : T.DerivationOf d s) : IsFormulaSet L s := by
  simpa [h.1] using h.2.case.1

lemma axL {s p : V} (hs : IsFormulaSet L s) (h : p ∈ s) (hn : neg L p ∈ s) : T.Derivation (axL s p) :=
  Theory.Derivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

lemma verumIntro {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    T.Derivation (verumIntro s) :=
  Theory.Derivation.mk ⟨by simpa using hs, Or.inr <| Or.inl ⟨s, rfl, h⟩⟩

lemma andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : T.DerivationOf dp (insert p s)) (hdq : T.DerivationOf dq (insert q s)) :
    T.Derivation (andIntro s p q dp dq) :=
  Theory.Derivation.mk ⟨by simp only [fstIdx_andIntro]; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

lemma orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : T.DerivationOf dpq (insert p (insert q s))) :
    T.Derivation (orIntro s p q dpq) :=
  Theory.Derivation.mk ⟨by simp only [fstIdx_orIntro]; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

lemma allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : T.DerivationOf dp (insert (free L p) (setShift L s))) :
    T.Derivation (allIntro s p dp) :=
  Theory.Derivation.mk
    ⟨by simp only [fstIdx_allIntro]; intro q hq; simpa using hdp.isFormulaSet (shift L q) (by simp [shift_mem_setShift hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, dp, rfl, h, hdp⟩⟩

lemma exsIntro {s p t dp : V}
    (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hdp : T.DerivationOf dp (insert (substs1 L t p) s)) :
    T.Derivation (exsIntro s p t dp) :=
  Theory.Derivation.mk
    ⟨by simp only [fstIdx_exsIntro]; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

lemma wkRule {s s' d : V} (hs : IsFormulaSet L s)
    (h : s' ⊆ s) (hd : T.DerivationOf d s') : T.Derivation (wkRule s d) :=
  Theory.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

lemma shiftRule {s d : V}
    (hd : T.DerivationOf d s) : T.Derivation (shiftRule (setShift L s) d) :=
  Theory.Derivation.mk
    ⟨by simp [hd.isFormulaSet],
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨setShift L s, d, rfl, by simp [hd.1], hd.2⟩⟩

lemma cutRule {s p d₁ d₂ : V}
    (hd₁ : T.DerivationOf d₁ (insert p s))
    (hd₂ : T.DerivationOf d₂ (insert (neg L p) s)) :
    T.Derivation (cutRule s p d₁ d₂) :=
  Theory.Derivation.mk
    ⟨by simp only [fstIdx_cutRule]; intro q hq; exact hd₁.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩⟩

lemma axm {s p : V} (hs : IsFormulaSet L s) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    T.Derivation (axm s p) :=
  Theory.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl, hp, hT⟩⟩

variable {U : Theory L} [U.Δ₁]

lemma of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {d : V} : T.Derivation d → U.Derivation d := by
  intro hd
  apply Theory.Derivation.induction1 𝚺 ?_ hd
  · intro s hs p hp hn; apply Derivation.axL hs hp hn
  · intro s hs hv; apply Derivation.verumIntro hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    apply Derivation.andIntro hpq ⟨hdp.1, ihp⟩ ⟨hdq.1, ihq⟩
  · intro s _ p q d hpq hd ih
    apply Derivation.orIntro hpq ⟨hd.1, ih⟩
  · intro s _ p d hp hd ih
    apply Derivation.allIntro hp ⟨hd.1, ih⟩
  · intro s _ p t d hp ht hd ih
    apply Derivation.exsIntro hp ht ⟨hd.1, ih⟩
  · intro s hs d h _ ih
    apply Derivation.wkRule hs h ⟨rfl, ih⟩
  · rintro s hs d rfl _ ih
    apply Derivation.shiftRule ⟨rfl, ih⟩
  · intro s _ p d₁ d₂ h₁ h₂ ih₁ ih₂
    apply Derivation.cutRule ⟨h₁.1, ih₁⟩ ⟨h₂.1, ih₂⟩
  · intro s hs p hps hpT
    apply Derivation.axm hs hps (h hpT)
  · definability

end Derivation

namespace Derivable

lemma isFormulaSet {s : V} (h : T.Derivable s) : IsFormulaSet L s := by
  rcases h with ⟨d, hd⟩; exact hd.isFormulaSet

lemma em {s : V} (hs : IsFormulaSet L s) (p) (h : p ∈ s) (hn : neg L p ∈ s) :
    T.Derivable s := ⟨axL s p, by simp, Derivation.axL hs h hn⟩

lemma verum {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    T.Derivable s := ⟨verumIntro s, by simp, Derivation.verumIntro hs h⟩

lemma and_m {s p q : V} (h : p ^⋏ q ∈ s) (hp : T.Derivable (insert p s)) (hq : T.Derivable (insert q s)) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩; rcases hq with ⟨dq, hdq⟩
  exact ⟨andIntro s p q dp dq, by simp, Derivation.andIntro h hdp hdq⟩

lemma or_m {s p q : V} (h : p ^⋎ q ∈ s) (hpq : T.Derivable (insert p (insert q s))) :
    T.Derivable s := by
  rcases hpq with ⟨dpq, hdpq⟩
  exact ⟨orIntro s p q dpq, by simp, Derivation.orIntro h hdpq⟩

lemma all_m {s p : V} (h : ^∀ p ∈ s) (hp : T.Derivable (insert (free L p) (setShift L s))) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨allIntro s p dp, by simp, Derivation.allIntro h hdp⟩

lemma ex_m {s p t : V} (h : ^∃ p ∈ s) (ht : IsTerm L t) (hp : T.Derivable (insert (substs1 L t p) s)) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨exsIntro s p t dp, by simp, Derivation.exsIntro h ht hdp⟩

lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : T.Derivable s') :
    T.Derivable s := by
  rcases hd with ⟨d, hd⟩
  exact ⟨wkRule s d, by simp, Derivation.wkRule hs h hd⟩

lemma shift {s : V} (hd : T.Derivable s) :
    T.Derivable (setShift L s) := by
  rcases hd with ⟨d, hd⟩
  exact ⟨shiftRule (setShift L s) d, by simp, Derivation.shiftRule hd⟩

lemma ofSetEq {s s' : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : T.Derivable s') :
    T.Derivable s := by
  have : s' = s := mem_ext h
  rcases this; exact hd

lemma exchange {s p q : V} (h : T.Derivable (insert p <| insert q s)) :
    T.Derivable (insert q <| insert p s) := h.ofSetEq (fun x ↦ by simp; tauto)

lemma cut {s : V} (p) (hd₁ : T.Derivable (insert p s)) (hd₂ : T.Derivable (insert (neg L p) s)) :
    T.Derivable s := by
  rcases hd₁ with ⟨d₁, hd₁⟩; rcases hd₂ with ⟨d₂, hd₂⟩
  exact ⟨cutRule s p d₁ d₂, by simp, Derivation.cutRule hd₁ hd₂⟩

lemma by_axm {s : V} (hs : IsFormulaSet L s) (p) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    T.Derivable s := by
  exact ⟨Bootstrapping.axm s p, by simp, Derivation.axm hs hp hT⟩

lemma of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {s : V} : T.Derivable s → U.Derivable s := by
  rintro ⟨d, hd⟩; exact ⟨d, hd.1, hd.2.of_ss h⟩

lemma and {s p q : V} (hp : T.Derivable (insert p s)) (hq : T.Derivable (insert q s)) :
    T.Derivable (insert (p ^⋏ q) s) :=
  and_m (p := p) (q := q) (by simp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hq)

lemma or {s p q : V} (hpq : T.Derivable (insert p (insert q s))) :
    T.Derivable (insert (p ^⋎ q) s) :=
  or_m (p := p) (q := q) (by simp)
    (wk (by simp [hpq.isFormulaSet.insert, hpq.isFormulaSet.insert.2.insert])
      (insert_subset_insert_of_subset _ <| insert_subset_insert_of_subset _ <| by simp) hpq)

/-- Crucial inducion for formalized $\Sigma_1$-completeness. -/
lemma conj (ps : V) {s : V} (hs : IsFormulaSet L s)
    (ds : ∀ i < len ps, T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋀ ps) s) := by
  have : ∀ k ≤ len ps, T.Derivable (insert (^⋀ (takeLast ps k)) s) := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa using verum (by simp [hs]) (by simp)
    case succ k ih =>
      have ih : T.Derivable (insert (^⋀ takeLast ps k) s) := ih (le_trans le_self_add hk)
      have : T.Derivable (insert ps.[len ps - (k + 1)] s) := ds (len ps - (k + 1)) ((tsub_lt_iff_left hk).mpr (by simp))
      simpa [takeLast_succ_of_lt (succ_le_iff_lt.mp hk)] using this.and ih
  simpa using this (len ps) (by rfl)

lemma disjDistr (ps s : V) (d : T.Derivable (vecToSet ps ∪ s)) : T.Derivable (insert (^⋁ ps) s) := by
  have : ∀ k ≤ len ps, ∀ s' ≤ vecToSet ps, s' ⊆ vecToSet ps →
      (∀ i < len ps - k, ps.[i] ∈ s') → T.Derivable (insert (^⋁ takeLast ps k) (s' ∪ s)) := by
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
      have : T.Derivable (insert (^⋁ takeLast ps k) (s'' ∪ s)) := by
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
  (hi : i < len ps) (d : T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋁ ps) s) :=
  disjDistr ps s <| wk
    (by suffices IsFormulaSet L (vecToSet ps) by simpa [by simpa using d.isFormulaSet]
        intro x hx; rcases mem_vecToSet_iff.mp hx with ⟨i, hi, rfl⟩; exact hps i hi)
    (by
      intro x; simp only [mem_bitInsert_iff, mem_cup_iff]
      rintro (rfl | hx)
      · left; exact mem_vecToSet_iff.mpr ⟨i, hi, rfl⟩
      · right; exact hx) d

lemma all {p s : V} (hp : IsSemiformula L 1 p) (dp : T.Derivable (insert (free L p) (setShift L s))) : T.Derivable (insert (^∀ p) s) :=
  all_m (p := p) (by simp) (wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp)

lemma exs {p t s : V} (hp : IsSemiformula L 1 p) (ht : IsTerm L t)
    (dp : T.Derivable (insert (substs1 L t p) s)) : T.Derivable (insert (^∃ p) s) :=
  ex_m (p := p) (by simp) ht <| wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp

end Derivable

lemma internal_provable_iff_internal_derivable {φ : V} : T.Provable φ ↔ T.Derivable (insert φ ∅ : V) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using hb⟩

alias ⟨Provable.toDerivable, Derivable.toProvable⟩ := internal_provable_iff_internal_derivable

namespace Provable

lemma conj (ps : V)
    (ds : ∀ i < len ps, T.Provable ps.[i]) : T.Provable (^⋀ ps) :=
  Derivable.toProvable <| Derivable.conj _ (by simp) fun i hi ↦ (ds i hi).toDerivable

lemma disj (ps : V) {i} (hps : ∀ i < len ps, IsFormula L ps.[i])
    (hi : i < len ps) (d : T.Provable ps.[i]) : T.Provable (^⋁ ps) :=
  Derivable.toProvable <| Derivable.disj _ _ hps hi d.toDerivable

end Provable

end LO.FirstOrder.Theory
