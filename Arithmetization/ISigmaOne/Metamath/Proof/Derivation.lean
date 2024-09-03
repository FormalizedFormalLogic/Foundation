import Arithmetization.ISigmaOne.Metamath.Proof.Thy

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT]

section derivation

variable (L)

def Language.IsFormulaSet (s : V) : Prop := ∀ p ∈ s, L.IsFormula p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.isFormulaSetDef (pL : LDef) : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “s. ∀ p ∈' s, !pL.isSemiformulaDef.sigma 0 p” (by simp))
  (.mkPi “s. ∀ p ∈' s, !pL.isSemiformulaDef.pi 0 p” (by simp))

variable (L)

lemma Language.isFormulaSet_defined : 𝚫₁-Predicate L.IsFormulaSet via pL.isFormulaSetDef :=
  ⟨by intro v; simp [LDef.isFormulaSetDef, HierarchySymbol.Semiformula.val_sigma, L.isSemiformula_defined.df.iff, L.isSemiformula_defined.proper.iff'],
   by intro v; simp [LDef.isFormulaSetDef, HierarchySymbol.Semiformula.val_sigma, L.isSemiformula_defined.df.iff]; rfl⟩

instance Language.isFormulaSet_definable : 𝚫₁-Predicate L.IsFormulaSet := L.isFormulaSet_defined.to_definable

instance Language.isFormulaSet_definable' : Γ-[m + 1]-Predicate L.IsFormulaSet := .of_deltaOne L.isFormulaSet_definable

end

@[simp] lemma Language.IsFormulaSet.empty : L.IsFormulaSet ∅ := fun p ↦ by simp

@[simp] lemma Language.IsFormulaSet.singleton {p} : L.IsFormulaSet {p} ↔ L.IsFormula p :=
  ⟨fun h ↦  h p (by simp), fun h p ↦ by
  simp only [mem_singleton_iff]
  rintro rfl; exact h⟩

@[simp] lemma Language.IsFormulaSet.insert_iff {p s} : L.IsFormulaSet (insert p s) ↔ L.IsFormula p ∧ L.IsFormulaSet s :=
  ⟨fun h ↦ ⟨h p (by simp), fun q hq ↦ h q (by simp [hq])⟩,
   by rintro ⟨hp, hs⟩ q; simp; rintro (rfl | hqs)
      · exact hp
      · exact hs q hqs⟩

alias ⟨Language.IsFormulaSet.insert, _⟩ := Language.IsFormulaSet.insert_iff

@[simp] lemma Language.IsFormulaSet.union {s₁ s₂} : L.IsFormulaSet (s₁ ∪ s₂) ↔ L.IsFormulaSet s₁ ∧ L.IsFormulaSet s₂ :=
  ⟨fun h ↦ ⟨fun p hp ↦ h p (by simp [hp]), fun p hp ↦ h p (by simp [hp])⟩,
   fun h p hp ↦ by
    rcases mem_cup_iff.mp hp with (h₁ | h₂)
    · exact h.1 p h₁
    · exact h.2 p h₂⟩

variable (L)

lemma setShift_existsUnique (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = L.shift x :=
  sigma₁_replacement (by definability) s

def Language.setShift (s : V) : V := Classical.choose! (setShift_existsUnique L s)

variable {L}

section setShift

lemma mem_setShift_iff {s y : V} : y ∈ L.setShift s ↔ ∃ x ∈ s, y = L.shift x :=
  Classical.choose!_spec (setShift_existsUnique L s) y

lemma Language.IsFormulaSet.setShift {s : V} (h : L.IsFormulaSet s) : L.IsFormulaSet (L.setShift s) := by
  simp [Language.IsFormulaSet, mem_setShift_iff]
  rintro _ p hp rfl; exact (h p hp).shift

lemma shift_mem_setShift {p s : V} (h : p ∈ s) : L.shift p ∈ L.setShift s :=
  mem_setShift_iff.mpr ⟨p, h, rfl⟩

@[simp] lemma Language.IsFormulaSet.setShift_iff {s : V} :
    L.IsFormulaSet (L.setShift s) ↔ L.IsFormulaSet s :=
  ⟨by intro h p hp; simpa using h (L.shift p) (shift_mem_setShift hp), Language.IsFormulaSet.setShift⟩

@[simp] lemma mem_setShift_union {s t : V} : L.setShift (s ∪ t) = L.setShift s ∪ L.setShift t := mem_ext <| by
  simp [mem_setShift_iff]; intro x
  constructor
  · rintro ⟨z, (hz | hz), rfl⟩
    · left; exact ⟨z, hz, rfl⟩
    · right; exact ⟨z, hz, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    exact ⟨z, Or.inl hz, rfl⟩
    exact ⟨z, Or.inr hz, rfl⟩

@[simp] lemma mem_setShift_insert {x s : V} : L.setShift (insert x s) = insert (L.shift x) (L.setShift s) := mem_ext <| by
  simp [mem_setShift_iff]

@[simp] lemma setShift_empty : L.setShift ∅ = ∅ := mem_ext <| by simp [mem_setShift_iff]

section

private lemma setShift_graph (t s : V) :
    t = L.setShift s ↔ (∀ y ∈ t, ∃ x ∈ s, y = L.shift x) ∧ (∀ x ∈ s, L.shift x ∈ t) := by
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

def _root_.LO.FirstOrder.Arith.LDef.setShiftDef (pL : LDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “t s. (∀ y ∈' t, ∃ x ∈' s, !pL.shiftDef y x) ∧ (∀ x ∈' s, ∃ y, !pL.shiftDef y x ∧ y ∈ t)” (by simp)

variable (L)

lemma Language.setShift_defined : 𝚺₁-Function₁ L.setShift via pL.setShiftDef := by
  intro v; simp [LDef.setShiftDef, setShift_graph, L.shift_defined.df.iff]

instance Language.setShift_definable : 𝚺₁-Function₁ L.setShift := L.setShift_defined.to_definable

end

end setShift

def axL (s p : V) : V := ⟪s, 0, p⟫ + 1

def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

def exIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

def wkRule (s d : V) : V := ⟪s, 6, d⟫ + 1

def shiftRule (s d : V) : V := ⟪s, 7, d⟫ + 1

def cutRule (s p d₁ d₂ : V) : V := ⟪s, 8, p, d₁, d₂⟫ + 1

def root (s p : V) : V := ⟪s, 9, p⟫ + 1

section

def _root_.LO.FirstOrder.Arith.axLDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 0 p ∧ y = y' + 1” (by simp)

lemma axL_defined : 𝚺₀-Function₂ (axL : V → V → V) via axLDef := by
  intro v; simp [axLDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_axLDef (v) :
    Semiformula.Evalbm V v axLDef.val ↔ v 0 = axL (v 1) (v 2) := axL_defined.df.iff v

def _root_.LO.FirstOrder.Arith.verumIntroDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “y s. ∃ y' < y, !pair₃Def y' s 1 0 ∧ y = y' + 1” (by simp)

lemma verumIntro_defined : 𝚺₀-Function₁ (verumIntro : V → V) via verumIntroDef := by
  intro v; simp [verumIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_verumIntroDef (v) :
    Semiformula.Evalbm V v verumIntroDef.val ↔ v 0 = verumIntro (v 1) := verumIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.andIntroDef : 𝚺₀.Semisentence 6 :=
  .mkSigma “y s p q dp dq. ∃ y' < y, !pair₆Def y' s 2 p q dp dq ∧ y = y' + 1” (by simp)

lemma andIntro_defined : 𝚺₀-Function₅ (andIntro : V → V → V → V → V → V) via andIntroDef := by
  intro v; simp [andIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_andIntroDef (v) :
    Semiformula.Evalbm V v andIntroDef.val ↔ v 0 = andIntro (v 1) (v 2) (v 3) (v 4) (v 5) := andIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.orIntroDef : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p q d. ∃ y' < y, !pair₅Def y' s 3 p q d ∧ y = y' + 1” (by simp)

lemma orIntro_defined : 𝚺₀-Function₄ (orIntro : V → V → V → V → V) via orIntroDef := by
  intro v; simp [orIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_orIntroDef (v) :
    Semiformula.Evalbm V v orIntroDef.val ↔ v 0 = orIntro (v 1) (v 2) (v 3) (v 4) := orIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.allIntroDef : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p d. ∃ y' < y, !pair₄Def y' s 4 p d ∧ y = y' + 1” (by simp)

lemma allIntro_defined : 𝚺₀-Function₃ (allIntro : V → V → V → V) via allIntroDef := by
  intro v; simp [allIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_allIntroDef (v) :
    Semiformula.Evalbm V v allIntroDef.val ↔ v 0 = allIntro (v 1) (v 2) (v 3) := allIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.exIntroDef : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p t d. ∃ y' < y, !pair₅Def y' s 5 p t d ∧ y = y' + 1” (by simp)

lemma exIntro_defined : 𝚺₀-Function₄ (exIntro : V → V → V → V → V) via exIntroDef := by
  intro v; simp [exIntroDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_exIntroDef (v) :
    Semiformula.Evalbm V v exIntroDef.val ↔ v 0 = exIntro (v 1) (v 2) (v 3) (v 4) := exIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.wkRuleDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 6 d ∧ y = y' + 1” (by simp)

lemma wkRule_defined : 𝚺₀-Function₂ (wkRule : V → V → V) via wkRuleDef := by
  intro v; simp [wkRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_wkRuleDef (v) :
    Semiformula.Evalbm V v wkRuleDef.val ↔ v 0 = wkRule (v 1) (v 2) := wkRule_defined.df.iff v

def _root_.LO.FirstOrder.Arith.shiftRuleDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s d. ∃ y' < y, !pair₃Def y' s 7 d ∧ y = y' + 1” (by simp)

lemma shiftRule_defined : 𝚺₀-Function₂ (shiftRule : V → V → V) via shiftRuleDef := by
  intro v; simp [shiftRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_shiftRuleDef (v) :
    Semiformula.Evalbm V v shiftRuleDef.val ↔ v 0 = shiftRule (v 1) (v 2) := shiftRule_defined.df.iff v

def _root_.LO.FirstOrder.Arith.cutRuleDef : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s p d₁ d₂. ∃ y' < y, !pair₅Def y' s 8 p d₁ d₂ ∧ y = y' + 1” (by simp)

lemma cutRule_defined : 𝚺₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleDef := by
  intro v; simp [cutRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_cutRuleDef (v) :
    Semiformula.Evalbm V v cutRuleDef.val ↔ v 0 = cutRule (v 1) (v 2) (v 3) (v 4) := cutRule_defined.df.iff v

def _root_.LO.FirstOrder.Arith.rootDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 9 p ∧ y = y' + 1” (by simp)

lemma root_defined : 𝚺₀-Function₂ (root : V → V → V) via rootDef := by
  intro v; simp [rootDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_rootDef (v) :
    Semiformula.Evalbm V v rootDef.val ↔ v 0 = root (v 1) (v 2) := root_defined.df.iff v

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

@[simp] lemma seq_lt_exIntro (s p t d : V) : s < exIntro s p t d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_exIntro (s p t d : V) : p < exIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma t_lt_exIntro (s p t d : V) : t < exIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d_lt_exIntro (s p t d : V) : d < exIntro s p t d :=
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

@[simp] lemma seq_lt_root (s p : V) : s < root s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_root (s p : V) : p < root s p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_axL (s p : V) : fstIdx (axL s p) = s := by simp [fstIdx, axL]
@[simp] lemma fstIdx_verumIntro (s : V) : fstIdx (verumIntro s) = s := by simp [fstIdx, verumIntro]
@[simp] lemma fstIdx_andIntro (s p q dp dq : V) : fstIdx (andIntro s p q dp dq) = s := by simp [fstIdx, andIntro]
@[simp] lemma fstIdx_orIntro (s p q dpq : V) : fstIdx (orIntro s p q dpq) = s := by simp [fstIdx, orIntro]
@[simp] lemma fstIdx_allIntro (s p d : V) : fstIdx (allIntro s p d) = s := by simp [fstIdx, allIntro]
@[simp] lemma fstIdx_exIntro (s p t d : V) : fstIdx (exIntro s p t d) = s := by simp [fstIdx, exIntro]
@[simp] lemma fstIdx_wkRule (s d : V) : fstIdx (wkRule s d) = s := by simp [fstIdx, wkRule]
@[simp] lemma fstIdx_shiftRule (s d : V) : fstIdx (shiftRule s d) = s := by simp [fstIdx, shiftRule]
@[simp] lemma fstIdx_cutRule (s p d₁ d₂ : V) : fstIdx (cutRule s p d₁ d₂) = s := by simp [fstIdx, cutRule]
@[simp] lemma fstIdx_root (s p : V) : fstIdx (root s p) = s := by simp [fstIdx, root]

end

namespace Derivation

abbrev conseq (x : V) : V := π₁ x

variable (T)

def Phi (C : Set V) (d : V) : Prop :=
  L.IsFormulaSet (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (L.free p) (L.setShift s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exIntro s p t dp ∧ ^∃ p ∈ s ∧ L.IsTerm t ∧ fstIdx dp = insert (L.substs₁ t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = L.setShift (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (L.neg p) s ∧ d₂ ∈ C)) ∨
    (∃ s p, d = root s p ∧ p ∈ s ∧ p ∈ T) )

private lemma phi_iff (C d : V) :
    Phi T {x | x ∈ C} d ↔
    L.IsFormulaSet (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
      (∃ s < d, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (L.free p) (L.setShift s) ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        d = exIntro s p t dp ∧ ^∃ p ∈ s ∧ L.IsTerm t ∧ fstIdx dp = insert (L.substs₁ t p) s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = shiftRule s d' ∧ s = L.setShift (fstIdx d') ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (L.neg p) s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        d = root s p ∧ p ∈ s ∧ p ∈ T) ) := by
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

def blueprint {pL : LDef} (pT : pL.TDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    (∃ fst, !fstIdxDef fst d ∧ !pL.isFormulaSetDef.sigma fst) ∧
    ( (∃ s < d, ∃ p < d, !axLDef d s p ∧ p ∈ s ∧ ∃ np, !pL.negDef np p ∧ np ∈ s) ∨
      (∃ s < d, !verumIntroDef d s ∧ ∃ vrm, !qqVerumDef vrm ∧ vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroDef d s p q dp dq ∧ (∃ and, !qqAndDef and p q ∧ and ∈ s) ∧
          (∃ c, !fstIdxDef c dp ∧ !insertDef c p s ∧ dp ∈ C) ∧
          (∃ c, !fstIdxDef c dq ∧ !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroDef d s p q dpq ∧ (∃ or, !qqOrDef or p q ∧ or ∈ s) ∧
        ∃ c, !fstIdxDef c dpq ∧ ∃ c', !insertDef c' q s ∧ !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroDef d s p dp ∧ (∃ all, !qqAllDef all p ∧ all ∈ s) ∧
        ∃ c, !fstIdxDef c dp ∧ ∃ fp, !pL.freeDef fp p ∧ ∃ ss, !pL.setShiftDef ss s ∧
        !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exIntroDef d s p t dp ∧ (∃ ex, !qqExDef ex p ∧ ex ∈ s) ∧
        !pL.isSemitermDef.sigma 0 t ∧ ∃ c, !fstIdxDef c dp ∧ ∃ pt, !pL.substs₁Def pt t p ∧ !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleDef d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleDef d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !pL.setShiftDef s c ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleDef d s p d₁ d₂ ∧
        (∃ c, !fstIdxDef c d₁ ∧ !insertDef c p s ∧ d₁ ∈ C) ∧
        (∃ c, !fstIdxDef c d₂ ∧ ∃ np, !pL.negDef np p ∧ !insertDef c np s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        !rootDef d s p ∧ p ∈ s ∧ !pT.ch.sigma p) )”
    (by simp))
  (.mkPi “d C.
    (∀ fst, !fstIdxDef fst d → !pL.isFormulaSetDef.pi fst) ∧
    ( (∃ s < d, ∃ p < d, !axLDef d s p ∧ p ∈ s ∧ ∀ np, !pL.negDef np p → np ∈ s) ∨
      (∃ s < d, !verumIntroDef d s ∧ ∀ vrm, !qqVerumDef vrm → vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroDef d s p q dp dq ∧ (∀ and, !qqAndDef and p q → and ∈ s) ∧
          (∀ c, !fstIdxDef c dp → !insertDef c p s ∧ dp ∈ C) ∧
          (∀ c, !fstIdxDef c dq → !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroDef d s p q dpq ∧ (∀ or, !qqOrDef or p q → or ∈ s) ∧
        ∀ c, !fstIdxDef c dpq → ∀ c', !insertDef c' q s → !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroDef d s p dp ∧ (∀ all, !qqAllDef all p → all ∈ s) ∧
        ∀ c, !fstIdxDef c dp → ∀ fp, !pL.freeDef fp p → ∀ ss, !pL.setShiftDef ss s →
          !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exIntroDef d s p t dp ∧ (∀ ex, !qqExDef ex p → ex ∈ s) ∧
        !pL.isSemitermDef.pi 0 t ∧
        ∀ c, !fstIdxDef c dp → ∀ pt, !pL.substs₁Def pt t p → !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleDef d s d' ∧ ∀ c, !fstIdxDef c d' → !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleDef d s d' ∧ ∀ c, !fstIdxDef c d' → ∀ ss, !pL.setShiftDef ss c → s = ss ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleDef d s p d₁ d₂ ∧
        (∀ c, !fstIdxDef c d₁ → !insertDef c p s ∧ d₁ ∈ C) ∧
        (∀ c, !fstIdxDef c d₂ → ∀ np, !pL.negDef np p → !insertDef c np s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        !rootDef d s p ∧ p ∈ s ∧ !pT.ch.pi p) )”
    (by simp))⟩

def construction : Fixpoint.Construction V (blueprint pT) where
  Φ := fun _ ↦ Phi T
  defined :=
  ⟨by
    intro v
    /-
    simp? [blueprint, HierarchySymbol.Semiformula.val_sigma,
      L.isFormulaSet_defined.df.iff, L.isFormulaSet_defined.proper.iff',
      L.neg_defined.df.iff,
      L.free_defined.df.iff,
      L.setShift_defined.df.iff,
      L.isSemiterm_defined.df.iff,
      L.isSemiterm_defined.proper.iff',
      L.substs₁_defined.df.iff,
      T.mem_defined.df.iff, T.mem_defined.proper.iff']
    -/
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, blueprint, Fin.isValue,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_and,
      Semiformula.eval_ex, Semiformula.eval_substs, Matrix.comp_vecCons', Semiterm.val_bvar,
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_fstIdxDef, L.isFormulaSet_defined.df.iff,
      LogicalConnective.Prop.and_eq, exists_eq_left, LogicalConnective.HomClass.map_or,
      Semiformula.eval_bexLT, Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, eval_axLDef, Semiformula.eval_operator₂, Structure.Mem.mem,
      L.neg_defined.df.iff, eval_verumIntroDef, eval_qqVerumDef, Matrix.cons_val_three,
      Fin.succ_one_eq_two, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_app_five,
      eval_andIntroDef, eval_qqAndDef, insert_defined_iff, Matrix.cons_app_seven,
      Matrix.cons_app_six, eval_orIntroDef, eval_qqOrDef, eval_allIntroDef, eval_qqAllDef,
      L.free_defined.df.iff, L.setShift_defined.df.iff, eval_exIntroDef, eval_qqExDef,
      Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
      L.isSemiterm_defined.df.iff, L.substs₁_defined.df.iff, eval_wkRuleDef, bitSubset_defined_iff,
      eval_shiftRuleDef, eval_cutRuleDef, eval_rootDef, T.mem_defined.df.iff,
      LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, L.isFormulaSet_defined.proper.iff',
      LogicalConnective.Prop.arrow_eq, forall_eq, L.isSemiterm_defined.proper.iff', Structure.Eq.eq,
      T.mem_defined.proper.iff']
    ,
  by
    intro v
    /-
    simp? [phi_iff, blueprint, HierarchySymbol.Semiformula.val_sigma,
      L.isFormulaSet_defined.df.iff,
      L.isFormulaSet_defined.proper.iff',
      L.neg_defined.df.iff,
      L.free_defined.df.iff,
      L.setShift_defined.df.iff,
      L.isSemiterm_defined.df.iff,
      L.isSemiterm_defined.proper.iff',
      L.substs₁_defined.df.iff,
      T.mem_defined.df.iff]
    -/
    simp only [Fin.isValue, phi_iff, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_and,
      Semiformula.eval_ex, Semiformula.eval_substs, Matrix.comp_vecCons', Semiterm.val_bvar,
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_fstIdxDef, L.isFormulaSet_defined.df.iff,
      LogicalConnective.Prop.and_eq, exists_eq_left, LogicalConnective.HomClass.map_or,
      Semiformula.eval_bexLT, Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, eval_axLDef, Semiformula.eval_operator₂, Structure.Mem.mem,
      L.neg_defined.df.iff, eval_verumIntroDef, eval_qqVerumDef, Matrix.cons_val_three,
      Fin.succ_one_eq_two, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_app_five,
      eval_andIntroDef, eval_qqAndDef, insert_defined_iff, Matrix.cons_app_seven,
      Matrix.cons_app_six, eval_orIntroDef, eval_qqOrDef, eval_allIntroDef, eval_qqAllDef,
      L.free_defined.df.iff, L.setShift_defined.df.iff, eval_exIntroDef, eval_qqExDef,
      Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
      L.isSemiterm_defined.df.iff, L.substs₁_defined.df.iff, eval_wkRuleDef, bitSubset_defined_iff,
      eval_shiftRuleDef, eval_cutRuleDef, eval_rootDef, T.mem_defined.df.iff,
      LogicalConnective.Prop.or_eq]
      ⟩
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

open Derivation

variable (T)

def Language.Theory.Derivation : V → Prop := (construction T).Fixpoint ![]

def Language.Theory.DerivationOf (d s : V) : Prop := fstIdx d = s ∧ T.Derivation d

def Language.Theory.Derivable (s : V) : Prop := ∃ d, T.DerivationOf d s

def Language.Theory.Provable (p : V) : Prop := T.Derivable {p}

section

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivationDef {pL : LDef} (pT : pL.TDef) : 𝚫₁.Semisentence 1 := (blueprint pT).fixpointDefΔ₁

lemma Language.Theory.derivation_defined : 𝚫₁-Predicate T.Derivation via pT.derivationDef := (construction T).fixpoint_definedΔ₁

instance Language.Theory.derivation_definable : 𝚫₁-Predicate T.Derivation := T.derivation_defined.to_definable

instance Language.Theory.derivation_definable' : Γ-[m + 1]-Predicate T.Derivation := T.derivation_definable.of_deltaOne

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivationOfDef {pL : LDef} (pT : pL.TDef) : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !pT.derivationDef.sigma d” (by simp))
  (.mkPi “d s. !fstIdxDef s d ∧ !pT.derivationDef.pi d” (by simp))

lemma Language.Theory.derivationOf_defined : 𝚫₁-Relation T.DerivationOf via pT.derivationOfDef :=
  ⟨by intro v; simp [LDef.TDef.derivationOfDef, HierarchySymbol.Semiformula.val_sigma, T.derivation_defined.proper.iff'],
   by intro v; simp [LDef.TDef.derivationOfDef, HierarchySymbol.Semiformula.val_sigma, T.derivation_defined.df.iff, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance Language.Theory.derivationOf_definable : 𝚫₁-Relation T.DerivationOf := T.derivationOf_defined.to_definable

instance Language.Theory.derivationOf_definable' : Γ-[m + 1]-Relation T.DerivationOf := T.derivationOf_definable.of_deltaOne

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivableDef {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 1 := .mkSigma
  “s. ∃ d, !pT.derivationOfDef.sigma d s” (by simp)

lemma Language.Theory.derivable_defined : 𝚺₁-Predicate T.Derivable via pT.derivableDef := by
  intro v; simp [LDef.TDef.derivableDef, HierarchySymbol.Semiformula.val_sigma, (derivationOf_defined T).df.iff, Language.Theory.Derivable]

instance Language.Theory.derivable_definable : 𝚺₁-Predicate T.Derivable := (derivable_defined T).to_definable

/-- instance for definability tactic-/
instance Language.Theory.derivable_definable' : 𝚺-[0 + 1]-Predicate T.Derivable := derivable_definable T

def _root_.LO.FirstOrder.Arith.LDef.TDef.prv {pL : LDef} (pT : pL.TDef) : 𝚺₁.Semisentence 1 := .mkSigma
  “p. ∃ s, !insertDef s p 0 ∧ !pT.derivableDef s” (by simp)

protected lemma Language.Theory.provable_defined : 𝚺₁-Predicate T.Provable via pT.prv := by
  intro v; simp [LDef.TDef.prv, (derivable_defined T).df.iff, Language.Theory.Provable, singleton_eq_insert, emptyset_def]

instance Language.Theory.provable_definable : 𝚺₁-Predicate T.Provable := T.provable_defined.to_definable

/-- instance for definability tactic-/
instance Language.Theory.provable_definable' : 𝚺-[0 + 1]-Predicate T.Provable := T.provable_definable

end

variable {T}

lemma Language.Theory.Derivation.case_iff {d : V} :
    T.Derivation d ↔
    L.IsFormulaSet (fstIdx d) ∧
    ( (∃ s p, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ T.DerivationOf dp (insert p s) ∧ T.DerivationOf dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ T.DerivationOf dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ T.DerivationOf dp (insert (L.free p) (L.setShift s))) ∨
      (∃ s p t dp, d = exIntro s p t dp ∧ ^∃ p ∈ s ∧ L.IsTerm t ∧ T.DerivationOf dp (insert (L.substs₁ t p) s)) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ T.Derivation d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = L.setShift (fstIdx d') ∧ T.Derivation d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ T.DerivationOf d₁ (insert p s) ∧ T.DerivationOf d₂ (insert (L.neg p) s)) ∨
      (∃ s p, d = root s p ∧ p ∈ s ∧ p ∈ T) ) :=
  (construction T).case

alias ⟨Language.Theory.Derivation.case, Language.Theory.Derivation.mk⟩ := Language.Theory.Derivation.case_iff

lemma Language.Theory.Derivation.induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    {d} (hd : T.Derivation d)
    (hAxL : ∀ s, L.IsFormulaSet s → ∀ p ∈ s, L.neg p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, L.IsFormulaSet s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, L.IsFormulaSet s → ∀ p q dp dq, p ^⋏ q ∈ s → T.DerivationOf dp (insert p s) → T.DerivationOf dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, L.IsFormulaSet s → ∀ p q d, p ^⋎ q ∈ s → T.DerivationOf d (insert p (insert q s)) →
      P d → P (orIntro s p q d))
    (hAll : ∀ s, L.IsFormulaSet s → ∀ p d, ^∀ p ∈ s → T.DerivationOf d (insert (L.free p) (L.setShift s)) →
      P d → P (allIntro s p d))
    (hEx : ∀ s, L.IsFormulaSet s → ∀ p t d, ^∃ p ∈ s → L.IsTerm t → T.DerivationOf d (insert (L.substs₁ t p) s) →
      P d → P (exIntro s p t d))
    (hWk : ∀ s, L.IsFormulaSet s → ∀ d, fstIdx d ⊆ s → T.Derivation d →
      P d → P (wkRule s d))
    (hShift : ∀ s, L.IsFormulaSet s → ∀ d, s = L.setShift (fstIdx d) → T.Derivation d →
      P d → P (shiftRule s d))
    (hCut : ∀ s, L.IsFormulaSet s → ∀ p d₁ d₂, T.DerivationOf d₁ (insert p s) → T.DerivationOf d₂ (insert (L.neg p) s) →
      P d₁ → P d₂ → P (cutRule s p d₁ d₂))
    (hRoot : ∀ s, L.IsFormulaSet s → ∀ p, p ∈ s → p ∈ T → P (root s p)) : P d :=
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
    · exact hEx s (by simpa using hds) p t d hp ht ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hWk s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hShift s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hCut s (by simpa using hds) p d₁ d₂ ⟨h₁, (ih d₁ hC₁).1⟩ ⟨h₂, (ih d₂ hC₂).1⟩ (ih d₁ hC₁).2 (ih d₂ hC₂).2
    · exact hRoot s (by simpa using hds) p hs hT) d hd

lemma Language.Theory.Derivation.isFormulaSet {d : V} (h : T.Derivation d) : L.IsFormulaSet (fstIdx d) := h.case.1

lemma Language.Theory.DerivationOf.isFormulaSet {d s : V} (h : T.DerivationOf d s) : L.IsFormulaSet s := by
  simpa [h.1] using h.2.case.1

lemma Language.Theory.Derivation.axL {s p : V} (hs : L.IsFormulaSet s) (h : p ∈ s) (hn : L.neg p ∈ s) : T.Derivation (axL s p) :=
  Language.Theory.Derivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

lemma Language.Theory.Derivation.verumIntro {s : V} (hs : L.IsFormulaSet s) (h : ^⊤ ∈ s) :
    T.Derivation (verumIntro s) :=
  Language.Theory.Derivation.mk ⟨by simpa using hs, Or.inr <| Or.inl ⟨s, rfl, h⟩⟩

lemma Language.Theory.Derivation.andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : T.DerivationOf dp (insert p s)) (hdq : T.DerivationOf dq (insert q s)) :
    T.Derivation (andIntro s p q dp dq) :=
  Language.Theory.Derivation.mk ⟨by simp; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

lemma Language.Theory.Derivation.orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : T.DerivationOf dpq (insert p (insert q s))) :
    T.Derivation (orIntro s p q dpq) :=
  Language.Theory.Derivation.mk ⟨by simp; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
    Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

lemma Language.Theory.Derivation.allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : T.DerivationOf dp (insert (L.free p) (L.setShift s))) :
    T.Derivation (allIntro s p dp) :=
  Language.Theory.Derivation.mk
    ⟨by simp; intro q hq; simpa using hdp.isFormulaSet (L.shift q) (by simp [shift_mem_setShift hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, dp, rfl, h, hdp⟩⟩

lemma Language.Theory.Derivation.exIntro {s p t dp : V}
    (h : ^∃ p ∈ s) (ht : L.IsTerm t)
    (hdp : T.DerivationOf dp (insert (L.substs₁ t p) s)) :
    T.Derivation (exIntro s p t dp) :=
  Language.Theory.Derivation.mk
    ⟨by simp; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

lemma Language.Theory.Derivation.wkRule {s s' d : V} (hs : L.IsFormulaSet s)
    (h : s' ⊆ s) (hd : T.DerivationOf d s') : T.Derivation (wkRule s d) :=
  Language.Theory.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

lemma Language.Theory.Derivation.shiftRule {s d : V}
    (hd : T.DerivationOf d s) : T.Derivation (shiftRule (L.setShift s) d) :=
  Language.Theory.Derivation.mk
    ⟨by simp [hd.isFormulaSet],
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨L.setShift s, d, rfl, by simp [hd.1], hd.2⟩⟩

lemma Language.Theory.Derivation.cutRule {s p d₁ d₂ : V}
    (hd₁ : T.DerivationOf d₁ (insert p s))
    (hd₂ : T.DerivationOf d₂ (insert (L.neg p) s)) :
    T.Derivation (cutRule s p d₁ d₂) :=
  Language.Theory.Derivation.mk
    ⟨by simp; intro q hq; exact hd₁.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩⟩

lemma Language.Theory.Derivation.root {s p : V} (hs : L.IsFormulaSet s) (hp : p ∈ s) (hT : p ∈ T) :
    T.Derivation (root s p) :=
  Language.Theory.Derivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl, hp, hT⟩⟩

variable {U : L.Theory} {pU : pL.TDef} [U.Defined pU]

lemma Language.Theory.Derivation.of_ss (h : T ⊆ U) {d : V} : T.Derivation d → U.Derivation d := by
  intro hd
  apply Language.Theory.Derivation.induction1 𝚺 ?_ hd
  · intro s hs p hp hn; apply axL hs hp hn
  · intro s hs hv; apply verumIntro hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    apply andIntro hpq ⟨hdp.1, ihp⟩ ⟨hdq.1, ihq⟩
  · intro s _ p q d hpq hd ih
    apply orIntro hpq ⟨hd.1, ih⟩
  · intro s _ p d hp hd ih
    apply allIntro hp ⟨hd.1, ih⟩
  · intro s _ p t d hp ht hd ih
    apply exIntro hp ht ⟨hd.1, ih⟩
  · intro s hs d h _ ih
    apply wkRule hs h ⟨rfl, ih⟩
  · rintro s hs d rfl _ ih
    apply shiftRule ⟨rfl, ih⟩
  · intro s _ p d₁ d₂ h₁ h₂ ih₁ ih₂
    apply cutRule ⟨h₁.1, ih₁⟩ ⟨h₂.1, ih₂⟩
  · intro s hs p hps hpT
    apply root hs hps (h hpT)
  · definability

namespace Language.Theory.Derivable

lemma isFormulaSet {s : V} (h : T.Derivable s) : L.IsFormulaSet s := by
  rcases h with ⟨d, hd⟩; exact hd.isFormulaSet

lemma em {s : V} (hs : L.IsFormulaSet s) (p) (h : p ∈ s) (hn : L.neg p ∈ s) :
    T.Derivable s := ⟨axL s p, by simp, Language.Theory.Derivation.axL hs h hn⟩

lemma verum {s : V} (hs : L.IsFormulaSet s) (h : ^⊤ ∈ s) :
    T.Derivable s := ⟨verumIntro s, by simp, Language.Theory.Derivation.verumIntro hs h⟩

lemma and_m {s p q : V} (h : p ^⋏ q ∈ s) (hp : T.Derivable (insert p s)) (hq : T.Derivable (insert q s)) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩; rcases hq with ⟨dq, hdq⟩
  exact ⟨andIntro s p q dp dq, by simp, Language.Theory.Derivation.andIntro h hdp hdq⟩

lemma or_m {s p q : V} (h : p ^⋎ q ∈ s) (hpq : T.Derivable (insert p (insert q s))) :
    T.Derivable s := by
  rcases hpq with ⟨dpq, hdpq⟩
  exact ⟨orIntro s p q dpq, by simp, Language.Theory.Derivation.orIntro h hdpq⟩

lemma all_m {s p : V} (h : ^∀ p ∈ s) (hp : T.Derivable (insert (L.free p) (L.setShift s))) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨allIntro s p dp, by simp, Language.Theory.Derivation.allIntro h hdp⟩

lemma ex_m {s p t : V} (h : ^∃ p ∈ s) (ht : L.IsTerm t) (hp : T.Derivable (insert (L.substs₁ t p) s)) :
    T.Derivable s := by
  rcases hp with ⟨dp, hdp⟩
  exact ⟨exIntro s p t dp, by simp, Language.Theory.Derivation.exIntro h ht hdp⟩

lemma wk {s s' : V} (hs : L.IsFormulaSet s) (h : s' ⊆ s) (hd : T.Derivable s') :
    T.Derivable s := by
  rcases hd with ⟨d, hd⟩
  exact ⟨wkRule s d, by simp, Language.Theory.Derivation.wkRule hs h hd⟩

lemma shift {s : V} (hd : T.Derivable s) :
    T.Derivable (L.setShift s) := by
  rcases hd with ⟨d, hd⟩
  exact ⟨shiftRule (L.setShift s) d, by simp, Language.Theory.Derivation.shiftRule hd⟩

lemma ofSetEq {s s' : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : T.Derivable s') :
    T.Derivable s := by
  have : s' = s := mem_ext h
  rcases this; exact hd

lemma cut {s : V} (p) (hd₁ : T.Derivable (insert p s)) (hd₂ : T.Derivable (insert (L.neg p) s)) :
    T.Derivable s := by
  rcases hd₁ with ⟨d₁, hd₁⟩; rcases hd₂ with ⟨d₂, hd₂⟩
  exact ⟨cutRule s p d₁ d₂, by simp, Language.Theory.Derivation.cutRule hd₁ hd₂⟩

lemma by_axm {s : V} (hs : L.IsFormulaSet s) (p) (hp : p ∈ s) (hT : p ∈ T) :
    T.Derivable s := by
  exact ⟨Arith.root s p, by simp, Language.Theory.Derivation.root hs hp hT⟩

lemma of_ss (h : T ⊆ U) {s : V} : T.Derivable s → U.Derivable s := by
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
lemma conj (ps : V) {s} (hs : L.IsFormulaSet s)
    (ds : ∀ i < len ps, T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋀ ps) s) := by
  have : ∀ k ≤ len ps, T.Derivable (insert (^⋀ (takeLast ps k)) s) := by
    intro k hk
    induction k using induction_sigma1
    · definability
    case zero => simpa using verum (by simp [hs]) (by simp)
    case succ k ih =>
      simp [takeLast_succ_of_lt (succ_le_iff_lt.mp hk)]
      have ih : T.Derivable (insert (^⋀ takeLast ps k) s) := ih (le_trans le_self_add hk)
      have : T.Derivable (insert ps.[len ps - (k + 1)] s) := ds (len ps - (k + 1)) ((tsub_lt_iff_left hk).mpr (by simp))
      exact this.and ih
  simpa using this (len ps) (by rfl)

lemma disjDistr (ps s : V) (d : T.Derivable (vecToSet ps ∪ s)) : T.Derivable (insert (^⋁ ps) s) := by
  have : ∀ k ≤ len ps, ∀ s' ≤ vecToSet ps, s' ⊆ vecToSet ps →
      (∀ i < len ps - k, ps.[i] ∈ s') → T.Derivable (insert (^⋁ takeLast ps k) (s' ∪ s)) := by
    intro k hk
    induction k using induction_sigma1
    · apply HierarchySymbol.Boldface.imp (by definability)
      apply HierarchySymbol.Boldface.ball_le (by definability)
      apply HierarchySymbol.Boldface.imp (by definability)
      apply HierarchySymbol.Boldface.imp (by definability)
      definability
    case zero =>
      intro s' _ ss hs'
      refine wk ?_ ?_ d
      · simp [by simpa using d.isFormulaSet]
        intro x hx
        exact d.isFormulaSet x (by simp [ss hx])
      · intro x
        simp only [mem_cup_iff, mem_vecToSet_iff, takeLast_zero, qqDisj_nil, mem_bitInsert_iff]
        rintro (⟨i, hi, rfl⟩ | hx)
        · right; left; exact hs' i (by simpa using hi)
        · right; right; exact hx
    case succ k ih =>
      intro s' _ ss hs'
      simp [takeLast_succ_of_lt (succ_le_iff_lt.mp hk)]
      apply Derivable.or
      let s'' := insert ps.[len ps - (k + 1)] s'
      have hs'' : s'' ⊆ vecToSet ps := by
        intro x; simp [s'']
        rintro (rfl | h)
        · exact mem_vecToSet_iff.mpr ⟨_, by simp [tsub_lt_iff_left hk], rfl⟩
        · exact ss h
      have : T.Derivable (insert (^⋁ takeLast ps k) (s'' ∪ s)) := by
        refine ih (le_trans (by simp) hk) s'' (le_of_subset hs'') hs'' ?_
        intro i hi
        have : i ≤ len ps - (k + 1) := by
          simpa [sub_sub] using le_sub_one_of_lt hi
        rcases lt_or_eq_of_le this with (hi | rfl)
        · simp [s'', hs' i hi]
        · simp [s'']
      exact ofSetEq (by intro x; simp [s'']; tauto) this
  simpa using this (len ps) (by rfl) ∅ (by simp [emptyset_def]) (by simp) (by simp)

lemma disj (ps s : V) {i} (hps : ∀ i < len ps, L.IsFormula ps.[i])
  (hi : i < len ps) (d : T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋁ ps) s) :=
  disjDistr ps s <| wk
    (by simp [by simpa using d.isFormulaSet]; intro x hx; rcases mem_vecToSet_iff.mp hx with ⟨i, hi, rfl⟩; exact hps i hi)
    (by
      intro x; simp only [mem_bitInsert_iff, mem_cup_iff]
      rintro (rfl | hx)
      · left; exact mem_vecToSet_iff.mpr ⟨i, hi, rfl⟩
      · right; exact hx) d

lemma all {p : V} (hp : L.IsSemiformula 1 p) (dp : T.Derivable (insert (L.free p) (L.setShift s))) : T.Derivable (insert (^∀ p) s) :=
  all_m (p := p) (by simp) (wk (by simp [hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp)

lemma ex {p t : V} (hp : L.IsSemiformula 1 p) (ht : L.IsTerm t)
    (dp : T.Derivable (insert (L.substs₁ t p) s)) : T.Derivable (insert (^∃ p) s) :=
  ex_m (p := p) (by simp) ht (wk (by simp [ht, hp, by simpa using dp.isFormulaSet]) (by intro x; simp; tauto) dp)

end Language.Theory.Derivable

end derivation

end LO.Arith
