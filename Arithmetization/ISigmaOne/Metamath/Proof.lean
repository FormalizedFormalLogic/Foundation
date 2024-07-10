import Arithmetization.ISigmaOne.Metamath.Formula.Functions

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section derivation

variable (L)

def Language.substs₁ (t u : V) : V := L.substs 0 !⟦t⟧ u

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.substs₁Def (pL : LDef) : 𝚺₁-Semisentence 3 := .mkSigma
  “ z t p | ∃ v, !seqConsDef v 0 t ∧ !pL.substsDef z 0 v p” (by simp)

variable (L)

lemma substs₁_defined : 𝚺₁-Function₂ L.substs₁ via pL.substs₁Def := by
  intro v; simp [LDef.substs₁Def, (substs_defined L).df.iff]; rfl

@[simp] instance substs₁_definable : 𝚺₁-Function₂ L.substs₁ := Defined.to_definable _ (substs₁_defined L)

end

variable (L)

def Language.free (p : V) : V := L.substs₁ ^&0 (L.shift p)

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.freeDef (pL : LDef) : 𝚺₁-Semisentence 2 := .mkSigma
  “q p | ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !pL.shiftDef sp p ∧ !pL.substs₁Def q fz sp” (by simp)

variable (L)

lemma free_defined : 𝚺₁-Function₁ L.free via pL.freeDef := by
  intro v; simp [LDef.freeDef, (shift_defined L).df.iff, (substs₁_defined L).df.iff, Language.free]

@[simp] instance free_definable : 𝚺₁-Function₁ L.free := Defined.to_definable _ (free_defined L)

end

variable (L)

def Language.FormulaSet (s : V) : Prop := ∀ p ∈ s, L.Formula p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.formulaSetDef (pL : LDef) : 𝚫₁-Semisentence 1 := .mkDelta
  (.mkSigma “s | ∀ p ∈' s, !pL.isSemiformulaDef.sigma 0 p” (by simp))
  (.mkPi “s | ∀ p ∈' s, !pL.isSemiformulaDef.pi 0 p” (by simp))

variable (L)

lemma formulaSet_defined : 𝚫₁-Predicate L.FormulaSet via pL.formulaSetDef :=
  ⟨by intro v; simp [LDef.formulaSetDef, HSemiformula.val_sigma, (semiformula_defined L).df.iff, (semiformula_defined L).proper.iff'],
   by intro v; simp [LDef.formulaSetDef, HSemiformula.val_sigma, (semiformula_defined L).df.iff]; rfl⟩

@[simp] instance formulaSet_definable : 𝚫₁-Predicate L.FormulaSet := Defined.to_definable _ (formulaSet_defined L)

end

variable (L)

lemma setShift_existsUnique (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = L.shift x :=
  sigma₁_replacement (by definability) s

def Language.setShift (s : V) : V := Classical.choose! (setShift_existsUnique L s)

variable {L}

lemma mem_setShift_iff {s y : V} : y ∈ L.setShift s ↔ ∃ x ∈ s, y = L.shift x :=
  Classical.choose!_spec (setShift_existsUnique L s) y

lemma Language.FormulaSet.setShift {s : V} (h : L.FormulaSet s) : L.FormulaSet (L.setShift s) := by
  simp [Language.FormulaSet, mem_setShift_iff]
  rintro _ p hp rfl; exact (h p hp).shift

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

def _root_.LO.FirstOrder.Arith.LDef.setShiftDef (pL : LDef) : 𝚺₁-Semisentence 2 := .mkSigma
  “t s | (∀ y ∈' t, ∃ x ∈' s, !pL.shiftDef y x) ∧ (∀ x ∈' s, ∃ y, !pL.shiftDef y x ∧ y ∈ t)” (by simp)

variable (L)

lemma setShift_defined : 𝚺₁-Function₁ L.setShift via pL.setShiftDef := by
  intro v; simp [LDef.setShiftDef, setShift_graph, (shift_defined L).df.iff]

@[simp, definability] instance setShift_definable : 𝚺₁-Function₁ L.setShift := Defined.to_definable _ (setShift_defined L)

end

def axL (s p : V) : V := ⟪s, 0, p⟫ + 1

def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

def exIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

def wkRule (s d : V) : V := ⟪s, 6, d⟫ + 1

def cutRule (s p d₁ d₂ : V) : V := ⟪s, 7, p, d₁, d₂⟫ + 1

section

def _root_.LO.FirstOrder.Arith.axLDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “y s p | ∃ y' < y, !pair₃Def y' s 0 p ∧ y = y' + 1” (by simp)

lemma axL_defined : 𝚺₀-Function₂ (axL : V → V → V) via axLDef := by
  intro v; simp [axLDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_axLDef (v) :
    Semiformula.Evalbm V v axLDef.val ↔ v 0 = axL (v 1) (v 2) := axL_defined.df.iff v

def _root_.LO.FirstOrder.Arith.verumIntroDef : 𝚺₀-Semisentence 2 :=
  .mkSigma “y s | ∃ y' < y, !pair₃Def y' s 1 0 ∧ y = y' + 1” (by simp)

lemma verumIntro_defined : 𝚺₀-Function₁ (verumIntro : V → V) via verumIntroDef := by
  intro v; simp [verumIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_verumIntroDef (v) :
    Semiformula.Evalbm V v verumIntroDef.val ↔ v 0 = verumIntro (v 1) := verumIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.andIntroDef : 𝚺₀-Semisentence 6 :=
  .mkSigma “y s p q dp dq | ∃ y' < y, !pair₆Def y' s 2 p q dp dq ∧ y = y' + 1” (by simp)

lemma andIntro_defined : 𝚺₀-Function₅ (andIntro : V → V → V → V → V → V) via andIntroDef := by
  intro v; simp [andIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_andIntroDef (v) :
    Semiformula.Evalbm V v andIntroDef.val ↔ v 0 = andIntro (v 1) (v 2) (v 3) (v 4) (v 5) := andIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.orIntroDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “y s p q d | ∃ y' < y, !pair₅Def y' s 3 p q d ∧ y = y' + 1” (by simp)

lemma orIntro_defined : 𝚺₀-Function₄ (orIntro : V → V → V → V → V) via orIntroDef := by
  intro v; simp [orIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_orIntroDef (v) :
    Semiformula.Evalbm V v orIntroDef.val ↔ v 0 = orIntro (v 1) (v 2) (v 3) (v 4) := orIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.allIntroDef : 𝚺₀-Semisentence 4 :=
  .mkSigma “y s p d | ∃ y' < y, !pair₄Def y' s 4 p d ∧ y = y' + 1” (by simp)

lemma allIntro_defined : 𝚺₀-Function₃ (allIntro : V → V → V → V) via allIntroDef := by
  intro v; simp [allIntroDef]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_allIntroDef (v) :
    Semiformula.Evalbm V v allIntroDef.val ↔ v 0 = allIntro (v 1) (v 2) (v 3) := allIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.exIntroDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “y s p t d | ∃ y' < y, !pair₅Def y' s 5 p t d ∧ y = y' + 1” (by simp)

lemma exIntro_defined : 𝚺₀-Function₄ (exIntro : V → V → V → V → V) via exIntroDef := by
  intro v; simp [exIntroDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_exIntroDef (v) :
    Semiformula.Evalbm V v exIntroDef.val ↔ v 0 = exIntro (v 1) (v 2) (v 3) (v 4) := exIntro_defined.df.iff v

def _root_.LO.FirstOrder.Arith.wkRuleDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “y s d | ∃ y' < y, !pair₃Def y' s 6 d ∧ y = y' + 1” (by simp)

lemma wkRule_defined : 𝚺₀-Function₂ (wkRule : V → V → V) via wkRuleDef := by
  intro v; simp [wkRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_wkRuleDef (v) :
    Semiformula.Evalbm V v wkRuleDef.val ↔ v 0 = wkRule (v 1) (v 2) := wkRule_defined.df.iff v

def _root_.LO.FirstOrder.Arith.cutRuleDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “y s p d₁ d₂ | ∃ y' < y, !pair₅Def y' s 7 p d₁ d₂ ∧ y = y' + 1” (by simp)

lemma cutRule_defined : 𝚺₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleDef := by
  intro v; simp [cutRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_cutRuleDef (v) :
    Semiformula.Evalbm V v cutRuleDef.val ↔ v 0 = cutRule (v 1) (v 2) (v 3) (v 4) := cutRule_defined.df.iff v

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

@[simp] lemma seq_lt_cutRule (s p d₁ d₂ : V) : s < cutRule s p d₁ d₂ := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_cutRule (s p d₁ d₂ : V) : p < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₁_lt_cutRule (s p d₁ d₂ : V) : d₁ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₂_lt_cutRule (s p d₁ d₂ : V) : d₂ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

end

namespace Derivation

abbrev conseq (x : V) : V := π₁ x

variable (L)

def Phi (C : Set V) (d : V) : Prop :=
  L.FormulaSet (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤[0] ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏[0] q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎[0] q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀[0] p ∈ s ∧ fstIdx dp = insert (L.free p) (L.setShift s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exIntro s p t dp ∧ ^∃[0] p ∈ s ∧ L.Term t ∧ fstIdx dp = insert (L.substs₁ t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (L.neg p) s ∧ d₂ ∈ C)) )

private lemma phi_iff (C d : V) :
    Phi L {x | x ∈ C} d ↔
    L.FormulaSet (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
      (∃ s < d, d = verumIntro s ∧ ^⊤[0] ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        d = andIntro s p q dp dq ∧ p ^⋏[0] q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        d = orIntro s p q dpq ∧ p ^⋎[0] q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        d = allIntro s p dp ∧ ^∀[0] p ∈ s ∧ fstIdx dp = insert (L.free p) (L.setShift s) ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        d = exIntro s p t dp ∧ ^∃[0] p ∈ s ∧ L.Term t ∧ fstIdx dp = insert (L.substs₁ t p) s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (L.neg p) s ∧ d₂ ∈ C)) ) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, p, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨s, p, q, dp, dq, rfl, h⟩ | ⟨s, p, q, dpq, rfl, h⟩ |
      ⟨s, p, dp, rfl, h⟩ | ⟨s, p, t, dp, rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, p, d₁, d₂, rfl, h⟩)
    · left; exact ⟨s, by simp, p, by simp, rfl, h⟩
    · right; left; exact ⟨s, by simp, rfl, h⟩
    · right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · right; right; right; left; exact ⟨s, by simp, p, by simp, q, by simp, dpq, by simp, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, by simp, p, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, by simp, p, by simp, t, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; exact ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, _, p, _, rfl, h⟩ | ⟨s, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dpq, _, rfl, h⟩ |
      ⟨s, _, p, _, dp, _, rfl, h⟩ | ⟨s, _, p, _, t, _, dp, _, rfl, h⟩ | ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, p, _, d₁, _, d₂, _, rfl, h⟩)
    · left; exact ⟨s, p, rfl, h⟩
    · right; left; exact ⟨s, rfl, h⟩
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, h⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, h⟩

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C |
    (∃ fst, !fstIdxDef fst d ∧ !pL.formulaSetDef.sigma fst) ∧
    ( (∃ s < d, ∃ p < d, !axLDef d s p ∧ p ∈ s ∧ ∃ np, !pL.negDef np p ∧ np ∈ s) ∨
      (∃ s < d, !verumIntroDef d s ∧ ∃ vrm, !qqVerumDef vrm 0 ∧ vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroDef d s p q dp dq ∧ (∃ and, !qqAndDef and 0 p q ∧ and ∈ s) ∧
          (∃ c, !fstIdxDef c dp ∧ !insertDef c p s ∧ dp ∈ C) ∧
          (∃ c, !fstIdxDef c dq ∧ !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroDef d s p q dpq ∧ (∃ or, !qqOrDef or 0 p q ∧ or ∈ s) ∧
        ∃ c, !fstIdxDef c dpq ∧ ∃ c', !insertDef c' q s ∧ !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroDef d s p dp ∧ (∃ all, !qqAllDef all 0 p ∧ all ∈ s) ∧
        ∃ c, !fstIdxDef c dp ∧ ∃ fp, !pL.freeDef fp p ∧ ∃ ss, !pL.setShiftDef ss s ∧
        !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exIntroDef d s p t dp ∧ (∃ ex, !qqExDef ex 0 p ∧ ex ∈ s) ∧
        !pL.isSemitermDef.sigma 0 t ∧ ∃ c, !fstIdxDef c dp ∧ ∃ pt, !pL.substs₁Def pt t p ∧ !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleDef d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleDef d s p d₁ d₂ ∧
        (∃ c, !fstIdxDef c d₁ ∧ !insertDef c p s ∧ d₁ ∈ C) ∧
        (∃ c, !fstIdxDef c d₂ ∧ ∃ np, !pL.negDef np p ∧ !insertDef c np s ∧ d₂ ∈ C)) )”
    (by simp))
  (.mkPi “d C |
    (∀ fst, !fstIdxDef fst d → !pL.formulaSetDef.pi fst) ∧
    ( (∃ s < d, ∃ p < d, !axLDef d s p ∧ p ∈ s ∧ ∀ np, !pL.negDef np p → np ∈ s) ∨
      (∃ s < d, !verumIntroDef d s ∧ ∀ vrm, !qqVerumDef vrm 0 → vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroDef d s p q dp dq ∧ (∀ and, !qqAndDef and 0 p q → and ∈ s) ∧
          (∀ c, !fstIdxDef c dp → !insertDef c p s ∧ dp ∈ C) ∧
          (∀ c, !fstIdxDef c dq → !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroDef d s p q dpq ∧ (∀ or, !qqOrDef or 0 p q → or ∈ s) ∧
        ∀ c, !fstIdxDef c dpq → ∀ c', !insertDef c' q s → !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroDef d s p dp ∧ (∀ all, !qqAllDef all 0 p → all ∈ s) ∧
        ∀ c, !fstIdxDef c dp → ∀ fp, !pL.freeDef fp p → ∀ ss, !pL.setShiftDef ss s →
          !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exIntroDef d s p t dp ∧ (∀ ex, !qqExDef ex 0 p → ex ∈ s) ∧
        !pL.isSemitermDef.pi 0 t ∧
        ∀ c, !fstIdxDef c dp → ∀ pt, !pL.substs₁Def pt t p → !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleDef d s d' ∧ ∀ c, !fstIdxDef c d' → !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        !cutRuleDef d s p d₁ d₂ ∧
        (∀ c, !fstIdxDef c d₁ → !insertDef c p s ∧ d₁ ∈ C) ∧
        (∀ c, !fstIdxDef c d₂ → ∀ np, !pL.negDef np p → !insertDef c np s ∧ d₂ ∈ C)) )”
    (by simp))⟩

def construction : Fixpoint.Construction V (blueprint pL) where
  Φ := fun _ ↦ Phi L
  defined := ⟨by
    intro v
    /-
    simp? [blueprint, HSemiformula.val_sigma,
      (formulaSet_defined L).df.iff, (formulaSet_defined L).proper.iff',
      (neg_defined L).df.iff,
      (free_defined L).df.iff,
      (setShift_defined L).df.iff,
      (isSemiterm_defined L).df.iff, (isSemiterm_defined L).proper.iff',
      (substs₁_defined L).df.iff]
    -/
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, blueprint, Fin.isValue, HSemiformula.val_sigma,
      HSemiformula.sigma_mkDelta, HSemiformula.val_mkSigma, LogicalConnective.HomClass.map_and,
      Semiformula.eval_ex, Semiformula.eval_substs, Matrix.comp_vecCons', Semiterm.val_bvar,
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_fstIdxDef, (formulaSet_defined L).df.iff,
      LogicalConnective.Prop.and_eq, exists_eq_left, LogicalConnective.HomClass.map_or,
      Semiformula.eval_bexLT, Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, eval_axLDef, Semiformula.eval_operator₂, Structure.Mem.mem,
      (neg_defined L).df.iff, eval_verumIntroDef, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingSymbol.zero_eq_zero, eval_qqVerumDef,
      Matrix.cons_val_three, Fin.succ_one_eq_two, Matrix.cons_val_four, Matrix.cons_val_succ,
      Matrix.cons_app_five, eval_andIntroDef, eval_qqAndDef, insert_defined_iff,
      Matrix.cons_app_seven, Matrix.cons_app_six, eval_orIntroDef, eval_qqOrDef, eval_allIntroDef,
      eval_qqAllDef, (free_defined L).df.iff, (setShift_defined L).df.iff, eval_exIntroDef,
      eval_qqExDef, (isSemiterm_defined L).df.iff, (substs₁_defined L).df.iff, eval_wkRuleDef,
      bitSubset_defined_iff, eval_cutRuleDef, LogicalConnective.Prop.or_eq, HSemiformula.pi_mkDelta,
      HSemiformula.val_mkPi, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      (formulaSet_defined L).proper.iff', LogicalConnective.Prop.arrow_eq, forall_eq,
      (isSemiterm_defined L).proper.iff'],
  by
    intro v
    /-
    simp? [phi_iff, blueprint, HSemiformula.val_sigma,
      (formulaSet_defined L).df.iff, (formulaSet_defined L).proper.iff',
      (neg_defined L).df.iff,
      (free_defined L).df.iff,
      (setShift_defined L).df.iff,
      (isSemiterm_defined L).df.iff, (isSemiterm_defined L).proper.iff',
      (substs₁_defined L).df.iff]
    -/
    simp only [Fin.isValue, phi_iff, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
      HSemiformula.val_sigma, HSemiformula.val_mkDelta, HSemiformula.val_mkSigma,
      LogicalConnective.HomClass.map_and, Semiformula.eval_ex, Semiformula.eval_substs,
      Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.constant_eq_singleton, eval_fstIdxDef,
      (formulaSet_defined L).df.iff, LogicalConnective.Prop.and_eq, exists_eq_left,
      LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, eval_axLDef,
      Semiformula.eval_operator₂, Structure.Mem.mem, (neg_defined L).df.iff, eval_verumIntroDef,
      Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingSymbol.zero_eq_zero,
      eval_qqVerumDef, Matrix.cons_val_three, Fin.succ_one_eq_two, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.cons_app_five, eval_andIntroDef, eval_qqAndDef,
      insert_defined_iff, Matrix.cons_app_seven, Matrix.cons_app_six, eval_orIntroDef, eval_qqOrDef,
      eval_allIntroDef, eval_qqAllDef, (free_defined L).df.iff, (setShift_defined L).df.iff,
      eval_exIntroDef, eval_qqExDef, (isSemiterm_defined L).df.iff, (substs₁_defined L).df.iff,
      eval_wkRuleDef, bitSubset_defined_iff, eval_cutRuleDef, LogicalConnective.Prop.or_eq]⟩
  monotone := by
    rintro C C' hC _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hC hpC⟩, ⟨hq, hC hqC⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hC hdC⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hC hdC⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hC hdC⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC hd₁C⟩, ⟨h₂, hC hd₂C⟩⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ | ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC, by simp⟩, ⟨hq, hqC, by simp⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hdC, by simp⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hdC, by simp⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hdC, by simp⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C, by simp⟩, ⟨h₂, hd₂C, by simp⟩⟩

end Derivation

open Derivation

variable (L)

def Language.Derivation : V → Prop := (construction L).Fixpoint ![]

def Language.DerivationOf (d s : V) : Prop := L.Derivation d ∧ s = conseq d

section

def _root_.LO.FirstOrder.Arith.LDef.derivationDef (pL : LDef) : 𝚫₁-Semisentence 1 := (blueprint pL).fixpointDefΔ₁

lemma derivation_defined : 𝚫₁-Predicate L.Derivation via pL.derivationDef := (construction L).fixpoint_definedΔ₁

instance derivation_definable : 𝚫₁-Predicate L.Derivation := Defined.to_definable _ (derivation_defined L)

@[simp] instance derivatin_definable' (Γ) : (Γ, m + 1)-Predicate L.Derivation :=
  .of_deltaOne (derivation_definable L) _ _

end

variable {L}

lemma Language.Derivation.case_iff {d : V} :
    L.Derivation d ↔
    L.FormulaSet (fstIdx d) ∧
    ( (∃ s p, d = axL s p ∧ p ∈ s ∧ L.neg p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤[0] ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏[0] q ∈ s ∧ (fstIdx dp = insert p s ∧ L.Derivation dp) ∧ (fstIdx dq = insert q s ∧ L.Derivation dq)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎[0] q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ L.Derivation dpq) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀[0] p ∈ s ∧ fstIdx dp = insert (L.free p) (L.setShift s) ∧ L.Derivation dp) ∨
      (∃ s p t dp, d = exIntro s p t dp ∧ ^∃[0] p ∈ s ∧ L.Term t ∧ fstIdx dp = insert (L.substs₁ t p) s ∧ L.Derivation dp) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ L.Derivation d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ L.Derivation d₁) ∧ (fstIdx d₂ = insert (L.neg p) s ∧ L.Derivation d₂)) ) :=
  (construction L).case

alias ⟨Language.Derivation.case, Language.Derivation.mk⟩ := Language.Derivation.case_iff

end derivation

end LO.Arith
