module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory

@[expose] public section
namespace LO

open FirstOrder Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

/-! ### Injectivity and disjointness of the constructors

All ten constructors have the shape `⟪s, k, …⟫ + 1` with a distinct tag `k` in the second
component, so they are injective and pairwise distinct. Together with the `fstIdx_*` and
`_lt_` lemmas above this is what lets a recursion on a code decide which rule produced it.
Each `_ne_` lemma is stated in the order the constructors are defined; use `.symm` for the
other orientation. -/

@[simp] lemma axL_inj {s p s' p' : V} : axL s p = axL s' p' ↔ s = s' ∧ p = p' := by simp [axL]

@[simp] lemma verumIntro_inj {s s' : V} : verumIntro s = verumIntro s' ↔ s = s' := by simp [verumIntro]

@[simp] lemma andIntro_inj {s p q dp dq s' p' q' dp' dq' : V} :
    andIntro s p q dp dq = andIntro s' p' q' dp' dq' ↔
      s = s' ∧ p = p' ∧ q = q' ∧ dp = dp' ∧ dq = dq' := by simp [andIntro]

@[simp] lemma orIntro_inj {s p q d s' p' q' d' : V} :
    orIntro s p q d = orIntro s' p' q' d' ↔ s = s' ∧ p = p' ∧ q = q' ∧ d = d' := by simp [orIntro]

@[simp] lemma allIntro_inj {s p d s' p' d' : V} :
    allIntro s p d = allIntro s' p' d' ↔ s = s' ∧ p = p' ∧ d = d' := by simp [allIntro]

@[simp] lemma exsIntro_inj {s p t d s' p' t' d' : V} :
    exsIntro s p t d = exsIntro s' p' t' d' ↔ s = s' ∧ p = p' ∧ t = t' ∧ d = d' := by simp [exsIntro]

@[simp] lemma wkRule_inj {s d s' d' : V} : wkRule s d = wkRule s' d' ↔ s = s' ∧ d = d' := by simp [wkRule]

@[simp] lemma shiftRule_inj {s d s' d' : V} :
    shiftRule s d = shiftRule s' d' ↔ s = s' ∧ d = d' := by simp [shiftRule]

@[simp] lemma cutRule_inj {s p d₁ d₂ s' p' d₁' d₂' : V} :
    cutRule s p d₁ d₂ = cutRule s' p' d₁' d₂' ↔ s = s' ∧ p = p' ∧ d₁ = d₁' ∧ d₂ = d₂' := by simp [cutRule]

@[simp] lemma axm_inj {s p s' p' : V} : axm s p = axm s' p' ↔ s = s' ∧ p = p' := by simp [axm]

@[simp] lemma axL_ne_verumIntro {s p s' : V} : axL s p ≠ verumIntro s' := by simp [axL, verumIntro]

@[simp] lemma axL_ne_andIntro {s p s' p' q' dp' dq' : V} :
    axL s p ≠ andIntro s' p' q' dp' dq' := by simp [axL, andIntro]

@[simp] lemma axL_ne_orIntro {s p s' p' q' d' : V} : axL s p ≠ orIntro s' p' q' d' := by simp [axL, orIntro]

@[simp] lemma axL_ne_allIntro {s p s' p' d' : V} : axL s p ≠ allIntro s' p' d' := by simp [axL, allIntro]

@[simp] lemma axL_ne_exsIntro {s p s' p' t' d' : V} : axL s p ≠ exsIntro s' p' t' d' := by simp [axL, exsIntro]

@[simp] lemma axL_ne_wkRule {s p s' d' : V} : axL s p ≠ wkRule s' d' := by simp [axL, wkRule]

@[simp] lemma axL_ne_shiftRule {s p s' d' : V} : axL s p ≠ shiftRule s' d' := by simp [axL, shiftRule]

@[simp] lemma axL_ne_cutRule {s p s' p' d₁' d₂' : V} : axL s p ≠ cutRule s' p' d₁' d₂' := by simp [axL, cutRule]

@[simp] lemma axL_ne_axm {s p s' p' : V} : axL s p ≠ axm s' p' := by simp [axL, axm]

@[simp] lemma verumIntro_ne_andIntro {s s' p' q' dp' dq' : V} :
    verumIntro s ≠ andIntro s' p' q' dp' dq' := by simp [verumIntro, andIntro]

@[simp] lemma verumIntro_ne_orIntro {s s' p' q' d' : V} :
    verumIntro s ≠ orIntro s' p' q' d' := by simp [verumIntro, orIntro]

@[simp] lemma verumIntro_ne_allIntro {s s' p' d' : V} :
    verumIntro s ≠ allIntro s' p' d' := by simp [verumIntro, allIntro]

@[simp] lemma verumIntro_ne_exsIntro {s s' p' t' d' : V} :
    verumIntro s ≠ exsIntro s' p' t' d' := by simp [verumIntro, exsIntro]

@[simp] lemma verumIntro_ne_wkRule {s s' d' : V} : verumIntro s ≠ wkRule s' d' := by simp [verumIntro, wkRule]

@[simp] lemma verumIntro_ne_shiftRule {s s' d' : V} :
    verumIntro s ≠ shiftRule s' d' := by simp [verumIntro, shiftRule]

@[simp] lemma verumIntro_ne_cutRule {s s' p' d₁' d₂' : V} :
    verumIntro s ≠ cutRule s' p' d₁' d₂' := by simp [verumIntro, cutRule]

@[simp] lemma verumIntro_ne_axm {s s' p' : V} : verumIntro s ≠ axm s' p' := by simp [verumIntro, axm]

@[simp] lemma andIntro_ne_orIntro {s p q dp dq s' p' q' d' : V} :
    andIntro s p q dp dq ≠ orIntro s' p' q' d' := by simp [andIntro, orIntro]

@[simp] lemma andIntro_ne_allIntro {s p q dp dq s' p' d' : V} :
    andIntro s p q dp dq ≠ allIntro s' p' d' := by simp [andIntro, allIntro]

@[simp] lemma andIntro_ne_exsIntro {s p q dp dq s' p' t' d' : V} :
    andIntro s p q dp dq ≠ exsIntro s' p' t' d' := by simp [andIntro, exsIntro]

@[simp] lemma andIntro_ne_wkRule {s p q dp dq s' d' : V} :
    andIntro s p q dp dq ≠ wkRule s' d' := by simp [andIntro, wkRule]

@[simp] lemma andIntro_ne_shiftRule {s p q dp dq s' d' : V} :
    andIntro s p q dp dq ≠ shiftRule s' d' := by simp [andIntro, shiftRule]

@[simp] lemma andIntro_ne_cutRule {s p q dp dq s' p' d₁' d₂' : V} :
    andIntro s p q dp dq ≠ cutRule s' p' d₁' d₂' := by simp [andIntro, cutRule]

@[simp] lemma andIntro_ne_axm {s p q dp dq s' p' : V} : andIntro s p q dp dq ≠ axm s' p' := by simp [andIntro, axm]

@[simp] lemma orIntro_ne_allIntro {s p q d s' p' d' : V} :
    orIntro s p q d ≠ allIntro s' p' d' := by simp [orIntro, allIntro]

@[simp] lemma orIntro_ne_exsIntro {s p q d s' p' t' d' : V} :
    orIntro s p q d ≠ exsIntro s' p' t' d' := by simp [orIntro, exsIntro]

@[simp] lemma orIntro_ne_wkRule {s p q d s' d' : V} : orIntro s p q d ≠ wkRule s' d' := by simp [orIntro, wkRule]

@[simp] lemma orIntro_ne_shiftRule {s p q d s' d' : V} :
    orIntro s p q d ≠ shiftRule s' d' := by simp [orIntro, shiftRule]

@[simp] lemma orIntro_ne_cutRule {s p q d s' p' d₁' d₂' : V} :
    orIntro s p q d ≠ cutRule s' p' d₁' d₂' := by simp [orIntro, cutRule]

@[simp] lemma orIntro_ne_axm {s p q d s' p' : V} : orIntro s p q d ≠ axm s' p' := by simp [orIntro, axm]

@[simp] lemma allIntro_ne_exsIntro {s p d s' p' t' d' : V} :
    allIntro s p d ≠ exsIntro s' p' t' d' := by simp [allIntro, exsIntro]

@[simp] lemma allIntro_ne_wkRule {s p d s' d' : V} : allIntro s p d ≠ wkRule s' d' := by simp [allIntro, wkRule]

@[simp] lemma allIntro_ne_shiftRule {s p d s' d' : V} :
    allIntro s p d ≠ shiftRule s' d' := by simp [allIntro, shiftRule]

@[simp] lemma allIntro_ne_cutRule {s p d s' p' d₁' d₂' : V} :
    allIntro s p d ≠ cutRule s' p' d₁' d₂' := by simp [allIntro, cutRule]

@[simp] lemma allIntro_ne_axm {s p d s' p' : V} : allIntro s p d ≠ axm s' p' := by simp [allIntro, axm]

@[simp] lemma exsIntro_ne_wkRule {s p t d s' d' : V} : exsIntro s p t d ≠ wkRule s' d' := by simp [exsIntro, wkRule]

@[simp] lemma exsIntro_ne_shiftRule {s p t d s' d' : V} :
    exsIntro s p t d ≠ shiftRule s' d' := by simp [exsIntro, shiftRule]

@[simp] lemma exsIntro_ne_cutRule {s p t d s' p' d₁' d₂' : V} :
    exsIntro s p t d ≠ cutRule s' p' d₁' d₂' := by simp [exsIntro, cutRule]

@[simp] lemma exsIntro_ne_axm {s p t d s' p' : V} : exsIntro s p t d ≠ axm s' p' := by simp [exsIntro, axm]

@[simp] lemma wkRule_ne_shiftRule {s d s' d' : V} : wkRule s d ≠ shiftRule s' d' := by simp [wkRule, shiftRule]

@[simp] lemma wkRule_ne_cutRule {s d s' p' d₁' d₂' : V} :
    wkRule s d ≠ cutRule s' p' d₁' d₂' := by simp [wkRule, cutRule]

@[simp] lemma wkRule_ne_axm {s d s' p' : V} : wkRule s d ≠ axm s' p' := by simp [wkRule, axm]

@[simp] lemma shiftRule_ne_cutRule {s d s' p' d₁' d₂' : V} :
    shiftRule s d ≠ cutRule s' p' d₁' d₂' := by simp [shiftRule, cutRule]

@[simp] lemma shiftRule_ne_axm {s d s' p' : V} : shiftRule s d ≠ axm s' p' := by simp [shiftRule, axm]

@[simp] lemma cutRule_ne_axm {s p d₁ d₂ s' p' : V} : cutRule s p d₁ d₂ ≠ axm s' p' := by simp [cutRule, axm]

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

namespace FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1 Derivation

variable (T)

def Derivation : V → Prop := (construction T).Fixpoint ![]

def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ Derivation T d

def Derivable (s : V) : Prop := ∃ d, DerivationOf T d s

def Proof (d φ : V) : Prop := DerivationOf T d {φ}

def Provable (φ : V) : Prop := ∃ d, Proof T d φ

noncomputable def derivation : 𝚫₁.Semisentence 1 := (blueprint T).fixpointDefΔ₁

noncomputable def derivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(derivation T).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(derivation T).pi d”)

noncomputable def derivable : 𝚺₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !(derivationOf T).sigma d Γ”

noncomputable def proof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !(derivationOf T).sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !(derivationOf T).pi d s”)

noncomputable def provable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ d, !(proof T).sigma d φ”

noncomputable abbrev provabilityPred (σ : Sentence L) : ArithmeticSentence := (provable T).val/[⌜σ⌝]

noncomputable def provabilityPred' (σ : Sentence L) : 𝚺₁.Sentence := .mkSigma
  “!(provable T) !!(⌜σ⌝)”

@[simp] lemma provabilityPred'_val (σ : Sentence L) : (provabilityPred' T σ).val = provabilityPred T σ := by rfl

variable {T}

section

instance Derivation.defined : 𝚫₁-Predicate[V] Derivation T via derivation T := (construction T).fixpoint_definedΔ₁

instance Derivation.definable : 𝚫₁-Predicate[V] Derivation T := Derivation.defined.to_definable

instance Derivation.definable' : Γ-[m + 1]-Predicate[V] Derivation T := Derivation.definable.of_deltaOne

instance DerivationOf.defined : 𝚫₁-Relation[V] DerivationOf T via derivationOf T := .mk
  ⟨by intro v; simp [derivationOf], by intro v; simp [derivationOf, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance DerivationOf.definable : 𝚫₁-Relation[V] DerivationOf T := DerivationOf.defined.to_definable

instance DerivationOf.definable' : Γ-[m + 1]-Relation[V] DerivationOf T := DerivationOf.definable.of_deltaOne

instance Derivable.defined : 𝚺₁-Predicate[V] Derivable T via derivable T := .mk fun v ↦ by simp [derivable, Derivable]

instance Derivable.definable : 𝚺₁-Predicate[V] Derivable T := Derivable.defined.to_definable

/-- instance for definability tactic-/
instance Derivable.definable' : 𝚺-[0 + 1]-Predicate[V] Derivable T := Derivable.definable

instance Proof.defined : 𝚫₁-Relation[V] Proof T via proof T := .mk
  ⟨by intro v; simp [proof], by intro v; simp [Proof, proof, singleton_eq_insert, emptyset_def]⟩

instance Proof.definable : 𝚫₁-Relation[V] Proof T := Proof.defined.to_definable

instance Proof.definable' : Γ-[m + 1]-Relation[V] Proof T := Proof.definable.of_deltaOne

instance Provable.defined : 𝚺₁-Predicate[V] Provable T via provable T := .mk fun v ↦ by simp [provable, Provable]

instance Provable.definable : 𝚺₁-Predicate[V] Provable T := Provable.defined.to_definable

/-- instance for definability tactic-/
instance Provable.definable' : 𝚺-[0 + 1]-Predicate[V] Provable T := Provable.definable

end

namespace Derivation

lemma case_iff {d : V} :
    Derivation T d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = Bootstrapping.axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ DerivationOf T dp (insert p s) ∧ DerivationOf T dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ DerivationOf T dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ DerivationOf T dp (insert (free L p) (setShift L s))) ∨
      (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ DerivationOf T dp (insert (substs1 L t p) s)) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ Derivation T d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ Derivation T d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ DerivationOf T d₁ (insert p s) ∧ DerivationOf T d₂ (insert (neg L p) s)) ∨
      (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) :=
  (construction T).case

alias ⟨case, _root_.LO.FirstOrder.Arithmetic.Bootstrapping.Derivation.mk⟩ := case_iff

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    {d} (hd : Derivation T d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s → DerivationOf T dp (insert p s) → DerivationOf T dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, IsFormulaSet L s → ∀ p q d, p ^⋎ q ∈ s → DerivationOf T d (insert p (insert q s)) →
      P d → P (orIntro s p q d))
    (hAll : ∀ s, IsFormulaSet L s → ∀ p d, ^∀ p ∈ s → DerivationOf T d (insert (free L p) (setShift L s)) →
      P d → P (allIntro s p d))
    (hExs : ∀ s, IsFormulaSet L s → ∀ p t d, ^∃ p ∈ s → IsTerm L t → DerivationOf T d (insert (substs1 L t p) s) →
      P d → P (exsIntro s p t d))
    (hWk : ∀ s, IsFormulaSet L s → ∀ d, fstIdx d ⊆ s → Derivation T d →
      P d → P (wkRule s d))
    (hShift : ∀ s, IsFormulaSet L s → ∀ d, s = setShift L (fstIdx d) → Derivation T d →
      P d → P (shiftRule s d))
    (hCut : ∀ s, IsFormulaSet L s → ∀ p d₁ d₂, DerivationOf T d₁ (insert p s) → DerivationOf T d₂ (insert (neg L p) s) →
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

lemma isFormulaSet {d : V} (h : Derivation T d) : IsFormulaSet L (fstIdx d) := (h : Derivation T d).case.1

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.DerivationOf.isFormulaSet {d s : V} (h : DerivationOf T d s) : IsFormulaSet L s := by
  simpa [h.1] using h.2.case.1

lemma axL {s p : V} (hs : IsFormulaSet L s) (h : p ∈ s) (hn : neg L p ∈ s) : Derivation T (axL s p) :=
  Bootstrapping.Derivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

lemma verumIntro {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    Derivation T (verumIntro s) :=
  Bootstrapping.Derivation.mk ⟨by simpa using hs, Or.inr <| Or.inl ⟨s, rfl, h⟩⟩

lemma andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : DerivationOf T dp (insert p s)) (hdq : DerivationOf T dq (insert q s)) :
    Derivation T (andIntro s p q dp dq) :=
  Bootstrapping.Derivation.mk ⟨by simp only [fstIdx_andIntro]; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

lemma orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : DerivationOf T dpq (insert p (insert q s))) :
    Derivation T (orIntro s p q dpq) :=
  Bootstrapping.Derivation.mk ⟨by simp only [fstIdx_orIntro]; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

lemma allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : DerivationOf T dp (insert (free L p) (setShift L s))) :
    Derivation T (allIntro s p dp) :=
  Bootstrapping.Derivation.mk
    ⟨by simp only [fstIdx_allIntro]; intro q hq; simpa using hdp.isFormulaSet (shift L q) (by simp [shift_mem_setShift hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, dp, rfl, h, hdp⟩⟩

lemma exsIntro {s p t dp : V}
    (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hdp : DerivationOf T dp (insert (substs1 L t p) s)) :
    Derivation T (exsIntro s p t dp) :=
  Bootstrapping.Derivation.mk
    ⟨by simp only [fstIdx_exsIntro]; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

lemma wkRule {s s' d : V} (hs : IsFormulaSet L s)
    (h : s' ⊆ s) (hd : DerivationOf T d s') : Derivation T (wkRule s d) :=
  Bootstrapping.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

lemma shiftRule {s d : V}
    (hd : DerivationOf T d s) : Derivation T (shiftRule (setShift L s) d) :=
  Bootstrapping.Derivation.mk
    ⟨by simp [hd.isFormulaSet],
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨setShift L s, d, rfl, by simp [hd.1], hd.2⟩⟩

lemma cutRule {s p d₁ d₂ : V}
    (hd₁ : DerivationOf T d₁ (insert p s))
    (hd₂ : DerivationOf T d₂ (insert (neg L p) s)) :
    Derivation T (cutRule s p d₁ d₂) :=
  Bootstrapping.Derivation.mk
    ⟨by simp only [fstIdx_cutRule]; intro q hq; exact hd₁.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩⟩

lemma axm {s p : V} (hs : IsFormulaSet L s) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    Derivation T (axm s p) :=
  Bootstrapping.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl, hp, hT⟩⟩

variable {U : Theory L} [U.Δ₁]

lemma of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {d : V} : Derivation T d → Derivation U d := by
  intro hd
  apply Bootstrapping.Derivation.induction1 𝚺 ?_ hd
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

lemma isFormulaSet {s : V} (h : Derivable T s) : IsFormulaSet L s := by
  rcases h with ⟨d, hd⟩; exact hd.isFormulaSet

lemma em {s : V} (hs : IsFormulaSet L s) (p) (h : p ∈ s) (hn : neg L p ∈ s) :
    Derivable T s := ⟨axL s p, by simp, Derivation.axL hs h hn⟩

lemma verum {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    Derivable T s := ⟨verumIntro s, by simp, Derivation.verumIntro hs h⟩

lemma and_m {s p q : V} (h : p ^⋏ q ∈ s) (hp : Derivable T (insert p s)) (hq : Derivable T (insert q s)) :
    Derivable T s := by
  rcases hp with ⟨dp, hdp⟩; rcases hq with ⟨dq, hdq⟩
  exact ⟨andIntro s p q dp dq, by simp, Derivation.andIntro h hdp hdq⟩

lemma or_m {s p q : V} (h : p ^⋎ q ∈ s) (hpq : Derivable T (insert p (insert q s))) :
    Derivable T s := by
  rcases hpq with ⟨dpq, hdpq⟩
  exact ⟨orIntro s p q dpq, by simp, Derivation.orIntro h hdpq⟩

lemma all_m {s p : V} (h : ^∀ p ∈ s) (hp : Derivable T (insert (free L p) (setShift L s))) :
    Derivable T s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨allIntro s p dp, by simp, Derivation.allIntro h hdp⟩

lemma ex_m {s p t : V} (h : ^∃ p ∈ s) (ht : IsTerm L t) (hp : Derivable T (insert (substs1 L t p) s)) :
    Derivable T s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨exsIntro s p t dp, by simp, Derivation.exsIntro h ht hdp⟩

lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : Derivable T s') :
    Derivable T s := by
  rcases hd with ⟨d, hd⟩
  exact ⟨wkRule s d, by simp, Derivation.wkRule hs h hd⟩

lemma shift {s : V} (hd : Derivable T s) :
    Derivable T (setShift L s) := by
  rcases hd with ⟨d, hd⟩
  exact ⟨shiftRule (setShift L s) d, by simp, Derivation.shiftRule hd⟩

lemma ofSetEq {s s' : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : Derivable T s') :
    Derivable T s := by
  have : s' = s := mem_ext h
  rcases this; exact hd

lemma exchange {s p q : V} (h : Derivable T (insert p <| insert q s)) :
    Derivable T (insert q <| insert p s) := h.ofSetEq (fun x ↦ by simp; tauto)

lemma cut {s : V} (p) (hd₁ : Derivable T (insert p s)) (hd₂ : Derivable T (insert (neg L p) s)) :
    Derivable T s := by
  rcases hd₁ with ⟨d₁, hd₁⟩; rcases hd₂ with ⟨d₂, hd₂⟩
  exact ⟨cutRule s p d₁ d₂, by simp, Derivation.cutRule hd₁ hd₂⟩

lemma by_axm {s : V} (hs : IsFormulaSet L s) (p) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    Derivable T s := by
  exact ⟨Bootstrapping.axm s p, by simp, Derivation.axm hs hp hT⟩

lemma of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {s : V} : Derivable T s → Derivable U s := by
  rintro ⟨d, hd⟩; exact ⟨d, hd.1, hd.2.of_ss h⟩

lemma and {s p q : V} (hp : Derivable T (insert p s)) (hq : Derivable T (insert q s)) :
    Derivable T (insert (p ^⋏ q) s) :=
  and_m (p := p) (q := q) (by simp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hp)
    (wk (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) (insert_subset_insert_of_subset _ <| by simp) hq)

lemma or {s p q : V} (hpq : Derivable T (insert p (insert q s))) :
    Derivable T (insert (p ^⋎ q) s) :=
  or_m (p := p) (q := q) (by simp)
    (wk (by simp [hpq.isFormulaSet.insert, hpq.isFormulaSet.insert.2.insert])
      (insert_subset_insert_of_subset _ <| insert_subset_insert_of_subset _ <| by simp) hpq)

/-- Crucial inducion for formalized $\Sigma_1$-completeness. -/
lemma conj (ps : V) {s : V} (hs : IsFormulaSet L s)
    (ds : ∀ i < len ps, Derivable T (insert ps.[i] s)) : Derivable T (insert (^⋀ ps) s) := by
  have : ∀ k ≤ len ps, Derivable T (insert (^⋀ (takeLast ps k)) s) := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa using verum (by simp [hs]) (by simp)
    case succ k ih =>
      have ih : Derivable T (insert (^⋀ takeLast ps k) s) := ih (le_trans le_self_add hk)
      have : Derivable T (insert ps.[len ps - (k + 1)] s) := ds (len ps - (k + 1)) ((tsub_lt_iff_left hk).mpr (by simp))
      simpa [takeLast_succ_of_lt (succ_le_iff_lt.mp hk)] using this.and ih
  simpa using this (len ps) (by rfl)

lemma disjDistr (ps s : V) (d : Derivable T (vecToSet ps ∪ s)) : Derivable T (insert (^⋁ ps) s) := by
  have : ∀ k ≤ len ps, ∀ s' ≤ vecToSet ps, s' ⊆ vecToSet ps →
      (∀ i < len ps - k, ps.[i] ∈ s') → Derivable T (insert (^⋁ takeLast ps k) (s' ∪ s)) := by
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
      have : Derivable T (insert (^⋁ takeLast ps k) (s'' ∪ s)) := by
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
  (hi : i < len ps) (d : Derivable T (insert ps.[i] s)) : Derivable T (insert (^⋁ ps) s) :=
  disjDistr ps s <| wk
    (by suffices IsFormulaSet L (vecToSet ps) by simpa [by simpa using d.isFormulaSet]
        intro x hx; rcases mem_vecToSet_iff.mp hx with ⟨i, hi, rfl⟩; exact hps i hi)
    (by
      intro x; simp only [mem_bitInsert_iff, mem_cup_iff]
      rintro (rfl | hx)
      · left; exact mem_vecToSet_iff.mpr ⟨i, hi, rfl⟩
      · right; exact hx) d

lemma all {p s : V} (hp : IsSemiformula L 1 p) (dp : Derivable T (insert (free L p) (setShift L s))) : Derivable T (insert (^∀ p) s) :=
  all_m (p := p) (by simp) (wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp)

lemma exs {p t s : V} (hp : IsSemiformula L 1 p) (ht : IsTerm L t)
    (dp : Derivable T (insert (substs1 L t p) s)) : Derivable T (insert (^∃ p) s) :=
  ex_m (p := p) (by simp) ht <| wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp

end Derivable

lemma internal_provable_iff_internal_derivable {φ : V} : Provable T φ ↔ Derivable T (insert φ ∅ : V) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using! hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using! hb⟩

alias ⟨Provable.toDerivable, Derivable.toProvable⟩ := internal_provable_iff_internal_derivable

namespace Provable

lemma conj (ps : V)
    (ds : ∀ i < len ps, Provable T ps.[i]) : Provable T (^⋀ ps) :=
  Derivable.toProvable <| Derivable.conj _ (by simp) fun i hi ↦ (ds i hi).toDerivable

lemma disj (ps : V) {i} (hps : ∀ i < len ps, IsFormula L ps.[i])
    (hi : i < len ps) (d : Provable T ps.[i]) : Provable T (^⋁ ps) :=
  Derivable.toProvable <| Derivable.disj _ _ hps hi d.toDerivable

end Provable

end LO.FirstOrder.Arithmetic.Bootstrapping
