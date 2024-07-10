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

def axL (s k R v : V) : V := ⟪s, 0, k, R, v⟫ + 1

def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

def exIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

def cutRule (s p d₁ d₂ : V) : V := ⟪s, 6, p, d₁, d₂⟫ + 1

section

def _root_.LO.FirstOrder.Arith.axLDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “y s k R v | ∃ y' < y, !pair₅Def y' s 0 k R v ∧ y = y' + 1” (by simp)

lemma axL_defined : 𝚺₀-Function₄ (axL : V → V → V → V → V) via axLDef := by
  intro v; simp [axLDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_axLDef (v) :
    Semiformula.Evalbm V v axLDef.val ↔ v 0 = axL (v 1) (v 2) (v 3) (v 4) := axL_defined.df.iff v

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

def _root_.LO.FirstOrder.Arith.cutRuleDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “y s p d₁ d₂ | ∃ y' < y, !pair₅Def y' s 6 p d₁ d₂ ∧ y = y' + 1” (by simp)

lemma cutRule_defined : 𝚺₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleDef := by
  intro v; simp [cutRuleDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_cutRuleDef (v) :
    Semiformula.Evalbm V v cutRuleDef.val ↔ v 0 = cutRule (v 1) (v 2) (v 3) (v 4) := cutRule_defined.df.iff v

@[simp] lemma seq_lt_axL (s k R v : V) : s < axL s k R v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_axL (s k R v : V) : k < axL s k R v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_axL (s k R v : V) : R < axL s k R v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_axL (s k R v : V) : v < axL s k R v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

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

@[simp] lemma seq_lt_cutRule (s p d₁ d₂ : V) : s < cutRule s p d₁ d₂ := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_cutRule (s p d₁ d₂ : V) : p < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₁_lt_cutRule (s p d₁ d₂ : V) : d₁ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₂_lt_cutRule (s p d₁ d₂ : V) : d₂ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

end
/-
namespace Derivation

abbrev conseq (x : V) : V := π₁ x

variable (L)

def Phi (C : Set V) (d : V) : Prop :=
  ∃ s d', d = ⟪s, d'⟫ + 1 ∧ L.FormulaSet s ∧
  ( (∃ p, p ∈ s ∧ L.neg p ∈ s ∧ d' = 0) ∨
    (^⊤[0] ∈ s ∧ d' = 0) ∨
    (∃ p q, p ^⋏[0] q ∈ s ∧ (conseq (π₁ d') = insert p s ∧ π₁ d' ∈ C) ∧ (conseq (π₂ d') = insert q s ∧ π₂ d' ∈ C)) ∨
    (∃ p q, p ^⋎[0] q ∈ s ∧ (conseq d' = insert p (insert q s) ∧ d' ∈ C)) ∨
    (∃ p, ^∀[0] p ∈ s ∧ (conseq d' = insert (L.free p) (L.setShift s) ∧ d' ∈ C)) ∨
    (∃ p, ^∃[0] p ∈ s ∧ (L.Term (π₁ d') ∧ conseq (π₂ d') = insert (L.substs₁ (π₁ d') p) s ∧ π₂ d' ∈ C)) )

private lemma phi_iff (C d : V) :
    Phi L {x | x ∈ C} d ↔
    ∃ s ≤ d, ∃ d' ≤ d, d = ⟪s, d'⟫ + 1 ∧ L.FormulaSet s ∧
    ( (∃ p < s, p ∈ s ∧ L.neg p ∈ s ∧ d' = 0) ∨
      (^⊤[0] ∈ s ∧ d' = 0) ∨
      (∃ p < s, ∃ q < s, p ^⋏[0] q ∈ s ∧
        (conseq (π₁ d') = insert p s ∧ π₁ d' ∈ C) ∧ (conseq (π₂ d') = insert q s ∧ π₂ d' ∈ C)) ∨
      (∃ p < s, ∃ q < s, p ^⋎[0] q ∈ s ∧ (conseq d' = insert p (insert q s) ∧ d' ∈ C)) ∨
      (∃ p < s, ^∀[0] p ∈ s ∧ (conseq d' = insert (L.free p) (L.setShift s) ∧ d' ∈ C)) ∨
      (∃ p < s, ^∃[0] p ∈ s ∧ (L.Term (π₁ d') ∧ conseq (π₂ d') = insert (L.substs₁ (π₁ d') p) s ∧ π₂ d' ∈ C)) ) := by
  constructor
  · rintro ⟨s, d', rfl, hs, H⟩
    refine ⟨s, le_trans (by simp) le_self_add, d', le_trans (by simp) le_self_add, rfl, hs, ?_⟩
    rcases H with (⟨p, hp, hnp⟩ | hs | ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · left; exact ⟨p, lt_of_mem hp, hp, hnp⟩
    · right; left; exact hs
    · right; right; left; exact ⟨p, lt_trans (by simp) (lt_of_mem hpq), q, lt_trans (by simp) (lt_of_mem hpq), hpq, h⟩
    · right; right; right; left; exact ⟨p, lt_trans (by simp) (lt_of_mem hpq), q, lt_trans (by simp) (lt_of_mem hpq), hpq, h⟩
    · right; right; right; right; left; exact ⟨p, lt_trans (by simp) (lt_of_mem hp), hp, h⟩
    · right; right; right; right; right; exact ⟨p, lt_trans (by simp) (lt_of_mem hp), hp, h⟩
  · rintro ⟨s, _, d', _, rfl, hs, H⟩
    refine ⟨s, d', rfl, hs, ?_⟩
    rcases H with (⟨p, _, h⟩ | hs | ⟨p, _, q, _, h⟩ | ⟨p, _, q, _, h⟩ | ⟨p, _, h⟩ | ⟨p, _, h⟩)
    · left; exact ⟨p, h⟩
    · right; left; exact hs
    · right; right; left; exact ⟨p, q, h⟩
    · right; right; right; left; exact ⟨p, q, h⟩
    · right; right; right; right; left; exact ⟨p, h⟩
    · right; right; right; right; right; exact ⟨p, h⟩

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C |
    ∃ s <⁺ d, ∃ d' <⁺ d, (∃ sd', !pairDef sd' s d' ∧ d = sd' + 1) ∧ !pL.formulaSetDef.sigma s ∧
    ( (∃ p < s, p ∈ s ∧ ∃ np, !pL.negDef np p ∧ np ∈ s ∧ d' = 0) ∨
      (∃ vrm, !qqVerumDef vrm 0 ∧ vrm ∈ s ∧ d' = 0) ∨
      (∃ p < s, ∃ q < s, (∃ and, !qqAndDef and 0 p q ∧ and ∈ s) ∧
        (∃ d₁, !pi₁Def d₁ d' ∧ (∃ c, !pi₁Def c d₁ ∧ !insertDef c p s) ∧ d₁ ∈ C) ∧
        (∃ d₂, !pi₂Def d₂ d' ∧ (∃ c, !pi₁Def c d₂ ∧ !insertDef c q s) ∧ d₂ ∈ C)) ∨
      (∃ p < s, ∃ q < s, (∃ or, !qqOrDef or 0 p q ∧ or ∈ s) ∧
        ((∃ c, !pi₁Def c d' ∧ ∃ c', !insertDef c' q s ∧ !insertDef c p c') ∧ d' ∈ C)) ∨
      (∃ p < s, (∃ all, !qqAllDef all 0 p ∧ all ∈ s) ∧
        ((∃ c, !pi₁Def c d' ∧ ∃ fp, !pL.freeDef fp p ∧ ∃ ss, !pL.setShiftDef ss s ∧ !insertDef c fp ss) ∧ d' ∈ C)) ∨
      (∃ p < s, (∃ ex, !qqExDef ex 0 p ∧ ex ∈ s) ∧
        (∃ t, !pi₁Def t d' ∧ !pL.isSemitermDef.sigma 0 t ∧ ∃ d₁, !pi₂Def d₁ d' ∧
          ∃ c, !pi₁Def c d₁ ∧ ∃ pt, !pL.substs₁Def pt t p ∧ !insertDef c pt s ∧ d₁ ∈ C)) )”
    (by simp))
  (.mkPi “d C |
    ∃ s <⁺ d, ∃ d' <⁺ d, (∀ sd', !pairDef sd' s d' → d = sd' + 1) ∧ !pL.formulaSetDef.pi s ∧
    ( (∃ p < s, p ∈ s ∧ ∀ np, !pL.negDef np p → np ∈ s ∧ d' = 0) ∨
      (∀ vrm, !qqVerumDef vrm 0 → vrm ∈ s ∧ d' = 0) ∨
      (∃ p < s, ∃ q < s, (∀ and, !qqAndDef and 0 p q → and ∈ s) ∧
        (∀ d₁, !pi₁Def d₁ d' → (∀ c, !pi₁Def c d₁ → !insertDef c p s) ∧ d₁ ∈ C) ∧
        (∀ d₂, !pi₂Def d₂ d' → (∀ c, !pi₁Def c d₂ → !insertDef c q s) ∧ d₂ ∈ C)) ∨
      (∃ p < s, ∃ q < s, (∀ or, !qqOrDef or 0 p q → or ∈ s) ∧
        ((∀ c, !pi₁Def c d' → ∀ c', !insertDef c' q s → !insertDef c p c') ∧ d' ∈ C)) ∨
      (∃ p < s, (∀ all, !qqAllDef all 0 p → all ∈ s) ∧
        ((∀ c, !pi₁Def c d' → ∀ fp, !pL.freeDef fp p → ∀ ss, !pL.setShiftDef ss s → !insertDef c fp ss) ∧ d' ∈ C)) ∨
      (∃ p < s, (∀ ex, !qqExDef ex 0 p → ex ∈ s) ∧
        (∀ t, !pi₁Def t d' → !pL.isSemitermDef.pi 0 t ∧ ∀ d₁, !pi₂Def d₁ d' →
          ∀ c, !pi₁Def c d₁ → ∀ pt, !pL.substs₁Def pt t p → !insertDef c pt s ∧ d₁ ∈ C)) )”
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
      HSemiformula.sigma_mkDelta, HSemiformula.val_mkSigma, Semiformula.eval_bexLTSucc',
      Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead, LogicalConnective.HomClass.map_and,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_two, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.constant_eq_singleton, pair_defined_iff, (formulaSet_defined L).df.iff,
      LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Semiformula.eval_operator₂,
      Structure.Mem.mem, Semiformula.eval_ex, (neg_defined L).df.iff, Matrix.cons_val_three,
      Fin.succ_one_eq_two, LogicalConnective.Prop.and_eq, exists_eq_left, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingSymbol.zero_eq_zero, eval_qqVerumDef, eval_qqAndDef,
      Matrix.cons_val_four, Matrix.cons_val_succ, pi₁_defined_iff, Matrix.cons_app_five,
      insert_defined_iff, Matrix.cons_app_six, pi₂_defined_iff, eval_qqOrDef, eval_qqAllDef,
      (free_defined L).df.iff, (setShift_defined L).df.iff, eval_qqExDef,
      (isSemiterm_defined L).df.iff, (substs₁_defined L).df.iff, Matrix.cons_app_eight,
      Matrix.cons_app_seven, LogicalConnective.Prop.or_eq, HSemiformula.pi_mkDelta,
      HSemiformula.val_mkPi, (formulaSet_defined L).proper.iff', Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq,
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
      Semiformula.eval_bexLTSucc', Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
      LogicalConnective.HomClass.map_and, Semiformula.eval_ex, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_fin_one,
      Matrix.constant_eq_singleton, pair_defined_iff, Semiformula.eval_operator₂,
      Matrix.cons_val_three, Fin.succ_one_eq_two, Semiterm.val_operator₂, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingSymbol.one_eq_one, Structure.Add.add, Structure.Eq.eq,
      LogicalConnective.Prop.and_eq, exists_eq_left, (formulaSet_defined L).df.iff,
      LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Structure.Mem.mem,
      (neg_defined L).df.iff, ORingSymbol.zero_eq_zero, eval_qqVerumDef, eval_qqAndDef,
      Matrix.cons_val_four, Matrix.cons_val_succ, pi₁_defined_iff, Matrix.cons_app_five,
      insert_defined_iff, Matrix.cons_app_six, pi₂_defined_iff, eval_qqOrDef, eval_qqAllDef,
      (free_defined L).df.iff, (setShift_defined L).df.iff, eval_qqExDef,
      (isSemiterm_defined L).df.iff, (substs₁_defined L).df.iff, Matrix.cons_app_eight,
      Matrix.cons_app_seven, LogicalConnective.Prop.or_eq]⟩
  monotone := by
    rintro C C' hC _ d ⟨s, d', rfl, hs, H⟩
    refine ⟨s, d', rfl, hs, ?_⟩
    rcases H with (h | h | ⟨p, q, hpq, ⟨h₁, h₁C⟩, ⟨h₂, h₂C⟩⟩ | ⟨p, q, hpq, h, hpC⟩ | ⟨p, hp, h, hpC⟩ | ⟨p, hp, ht, h, hpC⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact ⟨p, q, hpq, ⟨h₁, hC h₁C⟩, ⟨h₂, hC h₂C⟩⟩
    · right; right; right; left; exact ⟨p, q, hpq, h, hC hpC⟩
    · right; right; right; right; left; exact ⟨p, hp, h, hC hpC⟩
    · right; right; right; right; right; exact ⟨p, hp, ht, h, hC hpC⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨s, d', rfl, hs, H⟩
    refine ⟨s, d', rfl, hs, ?_⟩
    rcases H with (h | h | ⟨p, q, hpq, ⟨h₁, h₁C⟩, ⟨h₂, h₂C⟩⟩ | ⟨p, q, hpq, h, hpC⟩ | ⟨p, hp, h, hpC⟩ | ⟨p, hp, ht, h, hpC⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left
      exact ⟨p, q, hpq,
        ⟨h₁, h₁C, lt_succ_iff_le.mpr (le_trans (pi₁_le_self d') (le_pair_right s d'))⟩,
        ⟨h₂, h₂C, lt_succ_iff_le.mpr (le_trans (pi₂_le_self d') (le_pair_right s d'))⟩⟩
    · right; right; right; left
      exact ⟨p, q, hpq, h, hpC, lt_succ_iff_le.mpr (by simp)⟩
    · right; right; right; right; left
      exact ⟨p, hp, h, hpC, lt_succ_iff_le.mpr (by simp)⟩
    · right; right; right; right; right
      exact ⟨p, hp, ht, h, hpC, lt_succ_iff_le.mpr (le_trans (pi₂_le_self d') (le_pair_right s d'))⟩

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
    ∃ s d', d = ⟪s, d'⟫ + 1 ∧ L.FormulaSet s ∧
    ( (∃ p, p ∈ s ∧ L.neg p ∈ s ∧ d' = 0) ∨
      (^⊤[0] ∈ s ∧ d' = 0) ∨
      (∃ p q, p ^⋏[0] q ∈ s ∧ (conseq (π₁ d') = insert p s ∧ L.Derivation (π₁ d')) ∧ (conseq (π₂ d') = insert q s ∧ L.Derivation (π₂ d'))) ∨
      (∃ p q, p ^⋎[0] q ∈ s ∧ (conseq d' = insert p (insert q s) ∧ L.Derivation d')) ∨
      (∃ p, ^∀[0] p ∈ s ∧ (conseq d' = insert (L.free p) (L.setShift s) ∧ L.Derivation d')) ∨
      (∃ p, ^∃[0] p ∈ s ∧ (L.Term (π₁ d') ∧ conseq (π₂ d') = insert (L.substs₁ (π₁ d') p) s ∧ L.Derivation (π₂ d'))) ) :=
  (construction L).case

alias ⟨Language.Derivation.case_iff, Language.UFormula.mk⟩ := Language.Derivation.case_iff
-/
end derivation

end LO.Arith
