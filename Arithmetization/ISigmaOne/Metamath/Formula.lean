import Arithmetization.ISigmaOne.Metamath.Term
import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

def qqRel (n k r v : V) : V := ⟪n, 0, k, r, v⟫ + 1

def qqNRel (n k r v : V) : V := ⟪n, 1, k, r, v⟫ + 1

def qqVerum (n : V) : V := ⟪n, 2, 0⟫ + 1

def qqFalsum (n : V) : V := ⟪n, 3, 0⟫ + 1

def qqAnd (n p q : V) : V := ⟪n, 4, p, q⟫ + 1

def qqOr (n p q : V) : V := ⟪n, 5, p, q⟫ + 1

def qqAll (n p : V) : V := ⟪n, 6, p⟫ + 1

def qqEx (n p : V) : V := ⟪n, 7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤[" n "]" => qqVerum n

scoped notation "^⊥[" n "]" => qqFalsum n

scoped notation p:69 " ^⋏[" n "] " q:70 => qqAnd n p q

scoped notation p:68 " ^⋎[" n "] " q:69 => qqOr n p q

scoped notation "^∀[" n "] " p:64 => qqAll n p

scoped notation "^∃[" n "] " p:64 => qqEx n p

section

def _root_.LO.FirstOrder.Arith.qqRelDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “p n k r v | ∃ p' < p, !pair₅Def p' n 0 k r v ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqNRelDef : 𝚺₀-Semisentence 5 :=
  .mkSigma “p n k r v | ∃ p' < p, !pair₅Def p' n 1 k r v ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqVerumDef : 𝚺₀-Semisentence 2 :=
  .mkSigma “p n | ∃ p' < p, !pair₃Def p' n 2 0 ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqFalsumDef : 𝚺₀-Semisentence 2 :=
  .mkSigma “p n | ∃ p' < p, !pair₃Def p' n 3 0 ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqAndDef : 𝚺₀-Semisentence 4 :=
  .mkSigma “r n p q | ∃ r' < r, !pair₄Def r' n 4 p q ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqOrDef : 𝚺₀-Semisentence 4 :=
  .mkSigma “r n p q | ∃ r' < r, !pair₄Def r' n 5 p q ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqAllDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “r n p | ∃ r' < r, !pair₃Def r' n 6 p ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqExDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “r n p | ∃ r' < r, !pair₃Def r' n 7 p ∧ r = r' + 1” (by simp)

lemma ss (x : V) : x < x + 1 := by exact lt_add_one x

lemma qqRel_defined : 𝚺₀-Function₄ (qqRel : V → V → V → V → V) via qqRelDef := by
  intro v; simp [qqRelDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqNRel_defined : 𝚺₀-Function₄ (qqNRel : V → V → V → V → V) via qqNRelDef := by
  intro v; simp [qqNRelDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqVerum_defined : 𝚺₀-Function₁ (qqVerum : V → V) via qqVerumDef := by
  intro v; simp [qqVerumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqFalsum_defined : 𝚺₀-Function₁ (qqFalsum : V → V) via qqFalsumDef := by
  intro v; simp [qqFalsumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqAnd_defined : 𝚺₀-Function₃ (qqAnd : V → V → V → V) via qqAndDef := by
  intro v; simp [qqAndDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqOr_defined : 𝚺₀-Function₃ (qqOr : V → V → V → V) via qqOrDef := by
  intro v; simp [qqOrDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqForall_defined : 𝚺₀-Function₂ (qqAll : V → V → V) via qqAllDef := by
  intro v; simp [qqAllDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqExists_defined : 𝚺₀-Function₂ (qqEx : V → V → V) via qqExDef := by
  intro v; simp [qqExDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_qqRelDef (v) :
    Semiformula.Evalbm V v qqRelDef.val ↔ v 0 = ^rel (v 1) (v 2) (v 3) (v 4) := qqRel_defined.df.iff v

@[simp] lemma eval_qqNRelDef (v) :
    Semiformula.Evalbm V v qqNRelDef.val ↔ v 0 = ^nrel (v 1) (v 2) (v 3) (v 4) := qqNRel_defined.df.iff v

@[simp] lemma eval_qqVerumDef (v) :
    Semiformula.Evalbm V v qqVerumDef.val ↔ v 0 = ^⊤[v 1] := qqVerum_defined.df.iff v

@[simp] lemma eval_qqFalsumDef (v) :
    Semiformula.Evalbm V v qqFalsumDef.val ↔ v 0 = ^⊥[v 1] := qqFalsum_defined.df.iff v

@[simp] lemma eval_qqAndDef (v) :
    Semiformula.Evalbm V v qqAndDef.val ↔ v 0 = (v 2) ^⋏[v 1] (v 3) := qqAnd_defined.df.iff v

@[simp] lemma eval_qqOrDef (v) :
    Semiformula.Evalbm V v qqOrDef.val ↔ v 0 = (v 2) ^⋎[v 1] (v 3) := qqOr_defined.df.iff v

@[simp] lemma eval_qqAllDef (v) :
    Semiformula.Evalbm V v qqAllDef.val ↔ v 0 = ^∀[v 1] (v 2) := qqForall_defined.df.iff v

@[simp] lemma eval_qqExDef (v) :
    Semiformula.Evalbm V v qqExDef.val ↔ v 0 = ^∃[v 1] (v 2) := qqExists_defined.df.iff v

def bv (p : V) : V := π₁ (p - 1)

def _root_.LO.FirstOrder.Arith.bvDef : 𝚺₀-Semisentence 2 :=
  .mkSigma “n p | ∃ p' <⁺ p, !FirstOrder.Arith.sub p' p 1 ∧ !pi₁Def n p'” (by simp)

lemma bv_defined : 𝚺₀-Function₁ (bv : V → V) via bvDef := by
  intro v; simp [bvDef]
  constructor
  · intro h; exact ⟨v 1 - 1, by simp, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_bvDef (v) :
    Semiformula.Evalbm V v bvDef.val ↔ v 0 = bv (v 1) := bv_defined.df.iff v

instance bv_definable : 𝚺₀-Function₁ (bv : V → V) := Defined.to_definable _ bv_defined

instance bv_definable' (Γ) : Γ-Function₁ (bv : V → V) := .of_zero bv_definable _

end

@[simp] lemma bv_lt_rel (n k r v : V) : n < ^rel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_rel (n k r v : V) : k < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_rel (n k r v : V) : r < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_rel (n k r v : V) : v < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_nrel (n k r v : V) : n < ^nrel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_nrel (n k r v : V) : k < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (n k r v : V) : r < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_nrel (n k r v : V) : v < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_verum (n : V) : n < ^⊤[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma bv_lt_falsum (n : V) : n < ^⊥[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma bv_lt_and (n p q : V) : n < p ^⋏[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_and_left (n p q : V) : p < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_and_right (n p q : V) : q < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_or (n p q : V) : n < p ^⋎[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_or_left (n p q : V) : p < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (n p q : V) : q < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_forall (n p : V) : n < ^∀[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_forall (n p : V) : p < ^∀[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_exists (n p : V) : n < ^∃[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_exists (n p : V) : p < ^∃[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

namespace FormalizedFormula

variable (L)

def Phi (C : Set V) (p : V) : Prop :=
  (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^rel n k r v) ∨
  (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^nrel n k r v) ∨
  (∃ n, p = ^⊤[n]) ∨
  (∃ n, p = ^⊥[n]) ∨
  (∃ n q r, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋏[n] r) ∨
  (∃ n q r, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋎[n] r) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∀[n] q) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∃[n] q)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^rel n k r v) ∨
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^nrel n k r v) ∨
    (∃ n < p, p = ^⊤[n]) ∨
    (∃ n < p, p = ^⊥[n]) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋏[n] r) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋎[n] r) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∀[n] q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∃[n] q) where
  mp := by
    rintro (⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, k, r, v, hkr, hv, rfl⟩ | H)
    · left; refine ⟨n, ?_, k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    · right; left; refine ⟨n, ?_, k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    right; right
    rcases H with (⟨n, rfl⟩ | ⟨n, rfl⟩ | H)
    · left; exact ⟨n, by simp, rfl⟩
    · right; left; exact ⟨n, by simp, rfl⟩
    right; right
    rcases H with (⟨n, q, r, hp, hq, rfl⟩ | ⟨n, q, r, hp, hq, rfl⟩ | H)
    · left; refine ⟨n, ?_, q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    · right; left; refine ⟨n, ?_, q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    right; right
    rcases H with (⟨n, q, h, rfl⟩ | ⟨n, q, h, rfl⟩)
    · left; refine ⟨n, ?_, q, ?_, h, rfl⟩ <;> simp
    · right; refine ⟨n, ?_, q, ?_, h, rfl⟩ <;> simp
  mpr := by
    unfold Phi
    rintro (⟨n, _, k, _, r, _, v, _, hkr, hv, rfl⟩ | ⟨n, _, k, _, r, _, v, _, hkr, hv, rfl⟩ | H)
    · left; exact ⟨n, k, r, v, hkr, hv, rfl⟩
    · right; left; exact ⟨n, k, r, v, hkr, hv, rfl⟩
    right; right
    rcases H with (⟨n, _, rfl⟩ | ⟨n, _, rfl⟩ | H)
    · left; exact ⟨n, rfl⟩
    · right; left; exact ⟨n, rfl⟩
    right; right
    rcases H with (⟨n, _, q, _, r, _, hq, hr, rfl⟩ | ⟨n, _, q, _, r, _, hq, hr, rfl⟩ | H)
    · left; exact ⟨n, q, r, hq, hr, rfl⟩
    · right; left; exact ⟨n, q, r, hq, hr, rfl⟩
    right; right
    rcases H with (⟨n, _, q, _, hq, rfl⟩ | ⟨n, _, q, _, hq, rfl⟩)
    · left; exact ⟨n, q, hq, rfl⟩
    · right; exact ⟨n, q, hq, rfl⟩

def formulaAux : 𝚺₀-Semisentence 2 := .mkSigma
  “p C |
    (∃ n < p, !qqVerumDef p n) ∨
    (∃ n < p, !qqFalsumDef p n) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ !bvDef n q) ∧ (r ∈ C ∧ !bvDef n r) ∧ !qqAndDef p n q r) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ !bvDef n q) ∧ (r ∈ C ∧ !bvDef n r) ∧ !qqOrDef p n q r) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !bvDef (n + 1) q) ∧ !qqAllDef p n q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !bvDef (n + 1) q) ∧ !qqExDef p n q)”
  (by simp)

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma
    “p C |
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.termSeqDef.sigma k n v ∧ !qqRelDef p n k r v) ∨
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.termSeqDef.sigma k n v ∧ !qqNRelDef p n k r v) ∨
      !formulaAux p C” (by simp))
  (.mkPi
    “p C |
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.termSeqDef.pi k n v ∧ !qqRelDef p n k r v) ∨
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.termSeqDef.pi k n v ∧ !qqNRelDef p n k r v) ∨
      !formulaAux p C” (by simp))⟩

def construction : Fixpoint.Construction V (blueprint pL) where
  Φ := fun _ ↦ Phi L
  defined := ⟨
    by  intro v
        -- simp [blueprint, HSemiformula.val_sigma, (termSeq_defined L).proper.iff']
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, blueprint, Fin.isValue, HSemiformula.val_sigma,
          HSemiformula.sigma_mkDelta, HSemiformula.val_mkSigma, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          Matrix.cons_val_three, Fin.succ_one_eq_two, LogicalConnective.HomClass.map_and,
          Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, Matrix.constant_eq_singleton, Matrix.cons_val_four,
          Matrix.cons_val_succ, eval_qqRelDef, LogicalConnective.Prop.and_eq, eval_qqNRelDef,
          LogicalConnective.Prop.or_eq, HSemiformula.pi_mkDelta, HSemiformula.val_mkPi,
          (termSeq_defined L).proper.iff'],
    by  intro v
        -- simpa [blueprint, Language.Defined.eval_rel_iff (L := L), eval_termSeq L, HSemiformula.val_sigma, formulaAux] using phi_iff L _ _
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
          HSemiformula.val_sigma, formulaAux, HSemiformula.val_mkSigma,
          LogicalConnective.HomClass.map_or, HSemiformula.val_mkDelta, Semiformula.eval_bexLT,
          Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two,
          Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_three,
          Fin.succ_one_eq_two, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
          Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
          Matrix.constant_eq_singleton, Language.Defined.eval_rel_iff (L := L), eval_termSeq L,
          Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, eval_qqVerumDef, eval_qqFalsumDef, Semiformula.eval_operator₂,
          Structure.Mem.mem, eval_bvDef, eval_qqAndDef, eval_qqOrDef, Semiterm.val_operator₂,
          Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingSymbol.one_eq_one,
          Structure.Add.add, eval_qqAllDef, eval_qqExDef, LogicalConnective.Prop.or_eq] using
          phi_iff L _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨n, q, r, ⟨hqC, hq⟩, ⟨hrC, hr⟩, rfl⟩ | ⟨n, q, r, ⟨hqC, hq⟩, ⟨hrC, hr⟩, rfl⟩ | H)
    · left; exact ⟨n, q, r, ⟨hC hqC, hq⟩, ⟨hC hrC, hr⟩, rfl⟩
    · right; left; exact ⟨n, q, r, ⟨hC hqC, hq⟩, ⟨hC hrC, hr⟩, rfl⟩
    right; right
    rcases H with (⟨n, q, ⟨hqC, hq⟩, rfl⟩ | ⟨n, q, ⟨hqC, hq⟩, rfl⟩)
    · left; exact ⟨n, q, ⟨hC hqC, hq⟩, rfl⟩
    · right; exact ⟨n, q, ⟨hC hqC, hq⟩, rfl⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨n, q, r, ⟨hqC, hq⟩, ⟨hrC, hr⟩, rfl⟩ | ⟨n, q, r, ⟨hqC, hq⟩, ⟨hrC, hr⟩, rfl⟩ | H)
    · left; exact ⟨n, q, r, ⟨by simp [hqC], hq⟩, ⟨by simp [hrC], hr⟩, rfl⟩
    · right; left; exact ⟨n, q, r, ⟨by simp [hqC], hq⟩, ⟨by simp [hrC], hr⟩, rfl⟩
    right; right
    rcases H with (⟨n, q, ⟨hqC, hq⟩, rfl⟩ | ⟨n, q, ⟨hqC, hq⟩, rfl⟩)
    · left; exact ⟨n, q, ⟨by simp [hqC], hq⟩, rfl⟩
    · right; exact ⟨n, q, ⟨by simp [hqC], hq⟩, rfl⟩

end FormalizedFormula

section formula

open FormalizedFormula

variable (L)

def Language.IsUFormula : V → Prop := (construction L).Fixpoint ![]

def _root_.LO.FirstOrder.Arith.LDef.isUFormulaDef (pL : LDef) : 𝚫₁-Semisentence 1 :=
  (blueprint pL).fixpointDefΔ₁

lemma isUFormula_defined : 𝚫₁-Predicate L.IsUFormula via pL.isUFormulaDef :=
  (construction L).fixpoint_definedΔ₁

@[simp] lemma eval_isUFormulaDef (v) :
    Semiformula.Evalbm V v pL.isUFormulaDef.val ↔ L.IsUFormula (v 0) := (isUFormula_defined L).df.iff v

instance isUFormulaDef_definable : 𝚫₁-Predicate L.IsUFormula := Defined.to_definable _ (isUFormula_defined L)

@[simp, definability] instance isUFormulaDef_definable' (Γ) : (Γ, m + 1)-Predicate L.IsUFormula :=
  .of_deltaOne (isUFormulaDef_definable L) _ _

def Language.IsSemiformula (n p : V) : Prop := L.IsUFormula p ∧ bv p = n

def _root_.LO.FirstOrder.Arith.LDef.isSemiformulaDef (pL : LDef) : 𝚫₁-Semisentence 2 := .mkDelta
  (.mkSigma “n p | !pL.isUFormulaDef.sigma p ∧ !bvDef n p” (by simp))
  (.mkPi “n p | !pL.isUFormulaDef.pi p ∧ !bvDef n p” (by simp))

lemma isSemisentence_defined : 𝚫₁-Relation L.IsSemiformula via pL.isSemiformulaDef where
  left := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, (isUFormula_defined L).proper.iff']
  right := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, eval_isUFormulaDef L, Language.IsSemiformula, eq_comm]

variable {L}

local prefix:80 "𝐔 " => L.IsUFormula

lemma Language.IsUFormula.case_iff {p : V} :
    𝐔 p ↔
    (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^rel n k r v) ∨
    (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^nrel n k r v) ∨
    (∃ n, p = ^⊤[n]) ∨
    (∃ n, p = ^⊥[n]) ∨
    (∃ n q r, (𝐔 q ∧ n = bv q) ∧ (𝐔 r ∧ n = bv r) ∧ p = q ^⋏[n] r) ∨
    (∃ n q r, (𝐔 q ∧ n = bv q) ∧ (𝐔 r ∧ n = bv r) ∧ p = q ^⋎[n] r) ∨
    (∃ n q, (𝐔 q ∧ n + 1 = bv q) ∧ p = ^∀[n] q) ∨
    (∃ n q, (𝐔 q ∧ n + 1 = bv q) ∧ p = ^∃[n] q) :=
  (construction L).case

alias ⟨Language.IsUFormula.case, Language.IsUFormula.mk⟩ := Language.IsUFormula.case_iff

@[simp] lemma Language.IsUFormula.rel {n k r v : V} :
    𝐔 (^rel n k r v) ↔ L.Rel k r ∧ L.TermSeq k n v :=
  ⟨by intro h
      rcases h.case with (⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.nrel {n k r v : V} :
    𝐔 (^nrel n k r v) ↔ L.Rel k r ∧ L.TermSeq k n v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.verum (n : V) : 𝐔 ^⊤[n] :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.IsUFormula.falsum (n : V) : 𝐔 ^⊥[n] :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.IsUFormula.and {n p q : V} :
    𝐔 (p ^⋏[n] q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, ⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.or {n p q : V} :
    𝐔 (p ^⋎[n] q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, ⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.all {n p : V} :
    𝐔 (^∀[n] p) ↔ L.IsSemiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, hp, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp.1, Eq.symm hp.2⟩,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, p, ⟨hp.1, Eq.symm hp.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.ex {n p : V} :
    𝐔 (^∃[n] p) ↔ L.IsSemiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp.1, Eq.symm hp.2⟩,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨n, p, ⟨hp.1, Eq.symm hp.2⟩, rfl⟩)⟩

lemma Language.IsUFormula.induction (Γ) {P : V → Prop} (hP : (Γ, 1)-Predicate P)
    (hrel : ∀ n k r v, L.Rel k r → L.TermSeq k n v → P (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.TermSeq k n v → P (^nrel n k r v))
    (hverum : ∀ n, P ^⊤[n])
    (hfalsum : ∀ n, P ^⊥[n])
    (hand : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P p → P q → P (p ^⋏[n] q))
    (hor : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P p → P q → P (p ^⋎[n] q))
    (hall : ∀ n p, L.IsSemiformula (n + 1) p → P p → P (^∀[n] p))
    (hex : ∀ n p, L.IsSemiformula (n + 1) p → P p → P (^∃[n] p)) :
    ∀ p, 𝐔 p → P p :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
      ⟨n, p, q, ⟨hp, hnp⟩, ⟨hq, hnq⟩, rfl⟩ | ⟨n, p, q, ⟨hp, hnp⟩, ⟨hq, hnq⟩, rfl⟩ | ⟨n, p, ⟨hp, hnp⟩, rfl⟩ | ⟨n, p, ⟨hp, hnp⟩, rfl⟩)
    · exact hrel n k r v hkr hv
    · exact hnrel n k r v hkr hv
    · exact hverum n
    · exact hfalsum n
    · exact hand n p q ⟨(hC p hp).1, Eq.symm hnp⟩ ⟨(hC q hq).1, Eq.symm hnq⟩ (hC p hp).2 (hC q hq).2
    · exact hor n p q ⟨(hC p hp).1, Eq.symm hnp⟩ ⟨(hC q hq).1, Eq.symm hnq⟩ (hC p hp).2 (hC q hq).2
    · exact hall n p ⟨(hC p hp).1, Eq.symm hnp⟩ (hC p hp).2
    · exact hex n p ⟨(hC p hp).1, Eq.symm hnp⟩ (hC p hp).2)

end formula

namespace Language.UformulaRec

structure Blueprint (pL : LDef) (k : ℕ) where
  rel : 𝚺₁-Semisentence (k + 5)
  nrel : 𝚺₁-Semisentence (k + 5)
  verum : 𝚺₁-Semisentence (k + 2)
  falsum : 𝚺₁-Semisentence (k + 2)
  and : 𝚺₁-Semisentence (k + 6)
  or : 𝚺₁-Semisentence (k + 6)
  all : 𝚺₁-Semisentence (k + 4)
  ex : 𝚺₁-Semisentence (k + 4)

namespace Blueprint

variable {pL : LDef} (β : Blueprint pL k)

def blueprint (β : Blueprint pL k) : Fixpoint.Blueprint k := ⟨.mkDelta
  (.mkSigma “pr C |
    ∃ p <⁺ pr, ∃ r <⁺ pr, !pairDef pr p r ∧ !pL.isUFormulaDef.sigma p ∧
   ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p n k R v ∧ !β.rel.val r n k R v ⋯) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p n k R v ∧ !β.nrel.val r n k R v ⋯) ∨
    (∃ n < p, !qqVerumDef p n ∧ !β.verum.val r n ⋯) ∨
    (∃ n < p, !qqFalsumDef p n ∧ !β.falsum.val r n ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      p₁ ~[C] r₁ ∧ p₂ ~[C] r₂ ∧ !qqAndDef p n p₁ p₂ ∧ !β.and.val r n p₁ p₂ r₁ r₂ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      p₁ ~[C] r₁ ∧ p₂ ~[C] r₂ ∧ !qqOrDef p n p₁ p₂ ∧ !β.or.val r n p₁ p₂ r₁ r₂ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C,
      p₁ ~[C] r₁ ∧ !qqAllDef p n p₁ ∧ !β.all.val r n p₁ r₁ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C,
      p₁ ~[C] r₁ ∧ !qqExDef p n p₁ ∧ !β.ex.val r n p₁ r₁ ⋯))
  ” (by simp))
  (.mkPi “pr C |
    ∃ p <⁺ pr, ∃ r <⁺ pr, !pairDef pr p r ∧ !pL.isUFormulaDef.pi p ∧
    ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p n k R v ∧ !β.rel.graphDelta.pi.val r n k R v ⋯) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p n k R v ∧ !β.nrel.graphDelta.pi.val r n k R v ⋯) ∨
    (∃ n < p, !qqVerumDef p n ∧ !β.verum.graphDelta.pi.val r n ⋯) ∨
    (∃ n < p, !qqFalsumDef p n ∧ !β.falsum.graphDelta.pi.val r n ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      p₁ ~[C] r₁ ∧ p₂ ~[C] r₂ ∧ !qqAndDef p n p₁ p₂ ∧ !β.and.graphDelta.pi.val r n p₁ p₂ r₁ r₂ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      p₁ ~[C] r₁ ∧ p₂ ~[C] r₂ ∧ !qqOrDef p n p₁ p₂ ∧ !β.or.graphDelta.pi.val r n p₁ p₂ r₁ r₂ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C,
      p₁ ~[C] r₁ ∧ !qqAllDef p n p₁ ∧ !β.all.graphDelta.pi.val r n p₁ r₁ ⋯) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C,
      p₁ ~[C] r₁ ∧ !qqExDef p n p₁ ∧ !β.ex.graphDelta.pi.val r n p₁ r₁ ⋯))
  ” (by simp))⟩

def graph : 𝚺₁-Semisentence (k + 2) := .mkSigma
  “p r | ∃ pr <⁺ (p + r + 1)², !pairDef pr p r ∧ !β.blueprint.fixpointDef pr ⋯” (by simp)

def result : 𝚺₁-Semisentence (k + 2) := .mkSigma
  “r p | (!pL.isUFormulaDef.pi p → !β.graph p r ⋯) ∧ (¬!pL.isUFormulaDef.sigma p → r = 0)” (by simp)

end Blueprint

variable (V)

structure Construction (L : Arith.Language V) {k : ℕ} (φ : Blueprint pL k) where
  rel    : (Fin k → V) → V → V → V → V → V
  nrel   : (Fin k → V) → V → V → V → V → V
  verum  : (Fin k → V) → V → V
  falsum : (Fin k → V) → V → V
  and    : (Fin k → V) → V → V → V → V → V → V
  or     : (Fin k → V) → V → V → V → V → V → V
  all    : (Fin k → V) → V → V → V → V
  ex     : (Fin k → V) → V → V → V → V
  rel_defined    : DefinedFunction (fun v ↦ rel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.rel
  nrel_defined   : DefinedFunction (fun v ↦ nrel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.nrel
  verum_defined  : DefinedFunction (fun v ↦ verum (v ·.succ) (v 0)) φ.verum
  falsum_defined : DefinedFunction (fun v ↦ falsum (v ·.succ) (v 0)) φ.falsum
  and_defined    : DefinedFunction (fun v ↦ and (v ·.succ.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3) (v 4)) φ.and
  or_defined     : DefinedFunction (fun v ↦ or  (v ·.succ.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3) (v 4)) φ.or
  all_defined    : DefinedFunction (fun v ↦ all (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.all
  ex_defined     : DefinedFunction (fun v ↦ ex  (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.ex

variable {V}

namespace Construction

variable {β : Blueprint pL k} (c : Construction V L β)

def Phi (param : Fin k → V) (C : Set V) (pr : V) : Prop :=
  L.IsUFormula (π₁ pr) ∧ (
  (∃ n k r v, pr = ⟪^rel n k r v, c.rel param n k r v⟫) ∨
  (∃ n k r v, pr = ⟪^nrel n k r v, c.nrel param n k r v⟫) ∨
  (∃ n, pr = ⟪^⊤[n], c.verum param n⟫) ∨
  (∃ n, pr = ⟪^⊥[n], c.falsum param n⟫) ∨
  (∃ n p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪p ^⋏[n] q, c.and param n p q p' q'⟫) ∨
  (∃ n p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪p ^⋎[n] q, c.or param n p q p' q'⟫) ∨
  (∃ n p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪^∀[n] p, c.all param n p p'⟫) ∨
  (∃ n p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪^∃[n] p, c.ex param n p p'⟫) )

private lemma phi_iff (param : Fin k → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
    ∃ p ≤ pr, ∃ r ≤ pr, pr = ⟪p, r⟫ ∧ L.IsUFormula p ∧
    ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, p = ^rel n k R v ∧ r = c.rel param n k R v) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel n k R v ∧ r = c.nrel param n k R v) ∨
    (∃ n < p, p = ^⊤[n] ∧ r = c.verum param n) ∨
    (∃ n < p, p = ^⊥[n] ∧ r = c.falsum param n) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      ⟪p₁, r₁⟫ ∈ C ∧ ⟪p₂, r₂⟫ ∈ C ∧ p = p₁ ^⋏[n] p₂ ∧ r = c.and param n p₁ p₂ r₁ r₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ r₁ < C, ∃ r₂ < C,
      ⟪p₁, r₁⟫ ∈ C ∧ ⟪p₂, r₂⟫ ∈ C ∧ p = p₁ ^⋎[n] p₂ ∧ r = c.or param n p₁ p₂ r₁ r₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C, ⟪p₁, r₁⟫ ∈ C ∧ p = ^∀[n] p₁ ∧ r = c.all param n p₁ r₁) ∨
    (∃ n < p, ∃ p₁ < p, ∃ r₁ < C, ⟪p₁, r₁⟫ ∈ C ∧ p = ^∃[n] p₁ ∧ r = c.ex param n p₁ r₁)) where
  mp := by
    rintro ⟨hp, H⟩
    refine ⟨π₁ pr, by simp, π₂ pr, by simp, by simp, hp, ?_⟩
    rcases H with (⟨n, k, r, v, rfl⟩ | ⟨n, k, r, v, rfl⟩ | H)
    · left; exact ⟨n, by simp, k, by simp, r, by simp, v, by simp, by simp, by simp⟩
    · right; left; exact ⟨n, by simp, k, by simp, r, by simp, v, by simp⟩
    right; right
    rcases H with (⟨n, rfl⟩ | ⟨n, rfl⟩ | H)
    · left; exact ⟨n, by simp⟩
    · right; left; exact ⟨n, by simp⟩
    right; right
    rcases H with (⟨n, p, q, p', q', hpC, hqC, rfl⟩ | ⟨n, p, q, p', q', hpC, hqC, rfl⟩ | H)
    · left; exact ⟨n, by simp, p, by simp, q, by simp, p', lt_of_mem_rng hpC, q', lt_of_mem_rng hqC, hpC, hqC, by simp⟩
    · right; left; exact ⟨n, by simp, p, by simp, q, by simp, p', lt_of_mem_rng hpC, q', lt_of_mem_rng hqC, hpC, hqC, by simp⟩
    right; right
    rcases H with (⟨n, p₁, r₁, h₁, rfl⟩ | ⟨n, p₁, r₁, h₁, rfl⟩)
    · left; exact ⟨n, by simp, p₁, by simp, r₁, lt_of_mem_rng h₁, h₁, by simp⟩
    · right; exact ⟨n, by simp, p₁, by simp, r₁, lt_of_mem_rng h₁, h₁, by simp⟩
  mpr := by
    rintro ⟨p, _, r, _, rfl, hp, H⟩
    refine ⟨by simpa using hp, ?_⟩
    rcases H with (⟨n, _, k, _, R, _, v, _, rfl, rfl⟩ | ⟨n, _, k, _, R, _, v, _, rfl, rfl⟩ | H)
    · left; exact ⟨n, k, R, v, rfl⟩
    · right; left; exact ⟨n, k, R, v, rfl⟩
    right; right
    rcases H with (⟨n, _, rfl, rfl⟩ | ⟨n, _, rfl, rfl⟩ | H)
    · left; exact ⟨n, by rfl⟩
    · right; left; exact ⟨n, by rfl⟩
    right; right
    rcases H with (⟨n, _, p₁, _, p₂, _, r₁, _, r₂, _, h₁, h₂, rfl, rfl⟩ | ⟨n, _, p₁, _, p₂, _, r₁, _, r₂, _, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩
    · right; left; exact ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩
    right; right
    rcases H with (⟨n, _, p₁, _, r₁, _, h₁, rfl, rfl⟩ | ⟨n, _, p₁, _, r₁, _, h₁, rfl, rfl⟩)
    · left; exact ⟨n, p₁, r₁, h₁, rfl⟩
    · right; exact ⟨n, p₁, r₁, h₁, rfl⟩

def construction : Fixpoint.Construction V (β.blueprint) where
  Φ := c.Phi
  defined :=
  ⟨ by
      intro v
      /-
      simp? [HSemiformula.val_sigma, blueprint,
        eval_isUFormulaDef L, (isUFormula_defined L).proper.iff',
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.ex_defined.iff, c.ex_defined.graph_delta.proper.iff'
        ]
      -/
      simp only [Nat.succ_eq_add_one, Blueprint.blueprint, Nat.reduceAdd, HSemiformula.val_sigma,
        BinderNotation.finSuccItr_one, Nat.add_zero, HSemiformula.sigma_mkDelta,
        HSemiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
        Matrix.cons_val_one, Matrix.vecHead, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
        Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
        pair_defined_iff, Fin.isValue, Fin.succ_zero_eq_one, eval_isUFormulaDef L,
        Semiformula.eval_bexLT, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_app_five,
        eval_qqRelDef, Fin.succ_one_eq_two, c.rel_defined.iff, LogicalConnective.Prop.and_eq,
        eval_qqNRelDef, c.nrel_defined.iff, eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef,
        c.falsum_defined.iff, eval_qqAndDef, c.and_defined.iff, c.or_defined.iff, eval_qqAllDef,
        c.all_defined.iff, c.ex_defined.iff, LogicalConnective.Prop.or_eq, HSemiformula.pi_mkDelta,
        HSemiformula.val_mkPi, (isUFormula_defined L).proper.iff',
        c.rel_defined.graph_delta.proper.iff', HSemiformula.graphDelta_val,
        c.nrel_defined.graph_delta.proper.iff', c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.graph_delta.proper.iff', c.and_defined.graph_delta.proper.iff',
        c.or_defined.graph_delta.proper.iff', c.all_defined.graph_delta.proper.iff',
        c.ex_defined.graph_delta.proper.iff'],
    by  intro v
        /-
        simpa? [HSemiformula.val_sigma, blueprint,
          eval_isUFormulaDef L,
          c.rel_defined.iff,
          c.nrel_defined.iff,
          c.verum_defined.iff,
          c.falsum_defined.iff,
          c.and_defined.iff,
          c.or_defined.iff,
          c.all_defined.iff,
          c.ex_defined.iff] using c.phi_iff L _ _ _
        -/
        simpa only [Nat.succ_eq_add_one, BinderNotation.finSuccItr_one, Blueprint.blueprint, Nat.reduceAdd,
          HSemiformula.val_sigma, Nat.add_zero, HSemiformula.val_mkDelta, HSemiformula.val_mkSigma,
          Semiformula.eval_bexLTSucc', Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          pair_defined_iff, Fin.isValue, Fin.succ_zero_eq_one, eval_isUFormulaDef L,
          LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Matrix.cons_val_three,
          Matrix.cons_val_four, Matrix.cons_app_five, eval_qqRelDef, Fin.succ_one_eq_two,
          c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef, c.nrel_defined.iff,
          eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff,
          Matrix.cons_app_six, Matrix.cons_app_seven, Semiformula.eval_operator₃,
          Matrix.cons_app_eight, eval_memRel, eval_qqAndDef, c.and_defined.iff, eval_qqOrDef,
          c.or_defined.iff, eval_qqAllDef, c.all_defined.iff, eval_qqExDef, c.ex_defined.iff,
          LogicalConnective.Prop.or_eq] using c.phi_iff _ _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ pr ⟨hp, H⟩
    refine ⟨hp, ?_⟩
    rcases H with (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩ | ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩ | H)
    · left; exact ⟨n, p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl⟩
    · right; left; exact ⟨n, p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl⟩
    right; right
    rcases H with (⟨n, p₁, r₁, h₁, rfl⟩ | ⟨n, p₁, r₁, h₁, rfl⟩)
    · left; exact ⟨n, p₁, r₁, hC h₁, rfl⟩
    · right; exact ⟨n, p₁, r₁, hC h₁, rfl⟩

instance : c.construction.Finite where
  finite {C param pr h} := by
    rcases h with ⟨hp, (⟨n, k, R, v, rfl⟩ | ⟨n, k, R, v, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
      ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩ | ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl⟩ | ⟨n, p₁, r₁, h₁, rfl⟩ | ⟨n, p₁, r₁, h₁, rfl⟩ )⟩
    · exact ⟨0, hp, Or.inl ⟨n, k, R, v, rfl⟩⟩
    · exact ⟨0, hp, Or.inr <| Or.inl ⟨n, k, R, v, rfl⟩⟩
    · exact ⟨0, hp, Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩⟩
    · exact ⟨0, hp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩⟩
    · exact ⟨max ⟪p₁, r₁⟫ ⟪p₂, r₂⟫ + 1, hp, by
        right; right; right; right; left
        exact ⟨n, p₁, p₂, r₁, r₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl⟩⟩
    · exact ⟨max ⟪p₁, r₁⟫ ⟪p₂, r₂⟫ + 1, hp, by
        right; right; right; right; right; left
        exact ⟨n, p₁, p₂, r₁, r₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl⟩⟩
    · exact ⟨⟪p₁, r₁⟫ + 1, hp, by
        right; right; right; right; right; right; left
        exact ⟨n, p₁, r₁, by simp [h₁], rfl⟩⟩
    · exact ⟨⟪p₁, r₁⟫ + 1, hp, by
        right; right; right; right; right; right; right
        exact ⟨n, p₁, r₁, by simp [h₁], rfl⟩⟩

def Graph (param : Fin k → V) (x y : V) : Prop := c.construction.Fixpoint param ⟪x, y⟫

variable {param : Fin k → V}

variable {c}

lemma Graph.case_iff {p r : V} :
    c.Graph param p r ↔
    L.IsUFormula p ∧ (
    (∃ n k R v, p = ^rel n k R v ∧ r = c.rel param n k R v) ∨
    (∃ n k R v, p = ^nrel n k R v ∧ r = c.nrel param n k R v) ∨
    (∃ n, p = ^⊤[n] ∧ r = c.verum param n) ∨
    (∃ n, p = ^⊥[n] ∧ r = c.falsum param n) ∨
    (∃ n p₁ p₂ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ p = p₁ ^⋏[n] p₂ ∧ r = c.and param n p₁ p₂ r₁ r₂) ∨
    (∃ n p₁ p₂ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ p = p₁ ^⋎[n] p₂ ∧ r = c.or param n p₁ p₂ r₁ r₂) ∨
    (∃ n p₁ r₁, c.Graph param p₁ r₁ ∧ p = ^∀[n] p₁ ∧ r = c.all param n p₁ r₁) ∨
    (∃ n p₁ r₁, c.Graph param p₁ r₁ ∧ p = ^∃[n] p₁ ∧ r = c.ex param n p₁ r₁) ) :=
  Iff.trans c.construction.case (by
    apply and_congr (by simp)
    simp [Graph])

variable (c β)

lemma graph_defined : Arith.Defined (fun v ↦ c.Graph (v ·.succ.succ) (v 0) (v 1)) β.graph := by
  intro v
  simp [Blueprint.graph, c.construction.fixpoint_defined.iff]
  constructor
  · intro h; exact ⟨⟪v 0, v 1⟫, by simp, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v β.graph.val ↔ c.Graph (v ·.succ.succ) (v 0) (v 1) := (graph_defined β c).df.iff v

variable {β}

lemma graph_dom_isUFormula {p r} :
    c.Graph param p r → L.IsUFormula p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {n k r v y} (hkr : L.Rel k r) (hv : L.TermSeq k n v) :
    c.Graph param (^rel n k r v) y ↔ y = c.rel param n k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨n, k, r, v, H, rfl⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
      ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
    · simp [qqRel] at H; rcases H with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqRel, qqNRel] at H
    · simp [qqRel, qqVerum] at H
    · simp [qqRel, qqFalsum] at H
    · simp [qqRel, qqAnd] at H
    · simp [qqRel, qqOr] at H
    · simp [qqRel, qqAll] at H
    · simp [qqRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_nrel_iff {n k r v y} (hkr : L.Rel k r) (hv : L.TermSeq k n v) :
    c.Graph param (^nrel n k r v) y ↔ y = c.nrel param n k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, rfl⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
      ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
    · simp [qqNRel, qqRel] at H
    · simp [qqNRel] at H; rcases H with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqNRel, qqVerum] at H
    · simp [qqNRel, qqFalsum] at H
    · simp [qqNRel, qqAnd] at H
    · simp [qqNRel, qqOr] at H
    · simp [qqNRel, qqAll] at H
    · simp [qqNRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_verum_iff {n y} :
    c.Graph param ^⊤[n] y ↔ y = c.verum param n := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, rfl⟩ | ⟨_, H, _⟩ |
      ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
    · simp [qqVerum, qqRel] at H
    · simp [qqVerum, qqNRel] at H
    · simp [qqVerum, qqVerum] at H; rcases H; rfl
    · simp [qqVerum, qqFalsum] at H
    · simp [qqVerum, qqAnd] at H
    · simp [qqVerum, qqOr] at H
    · simp [qqVerum, qqAll] at H
    · simp [qqVerum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_falsum_iff {n y} :
    c.Graph param ^⊥[n] y ↔ y = c.falsum param n := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, rfl⟩ |
      ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
    · simp [qqFalsum, qqRel] at H
    · simp [qqFalsum, qqNRel] at H
    · simp [qqFalsum, qqVerum] at H
    · simp [qqFalsum, qqFalsum] at H; rcases H; rfl
    · simp [qqFalsum, qqAnd] at H
    · simp [qqFalsum, qqOr] at H
    · simp [qqFalsum, qqAll] at H
    · simp [qqFalsum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_rel {n k r v} (hkr : L.Rel k r) (hv : L.TermSeq k n v) :
    c.Graph param (^rel n k r v) (c.rel param n k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {n k r v} (hkr : L.Rel k r) (hv : L.TermSeq k n v) :
    c.Graph param (^nrel n k r v) (c.nrel param n k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_verum (n : V) :
    c.Graph param (^⊤[n]) (c.verum param n) :=
  (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_falsum (n : V) :
    c.Graph param (^⊥[n]) (c.falsum param n) :=
  (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_and {n p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsSemiformula n p₁) (hp₂ : L.IsSemiformula n p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋏[n] p₂) (c.and param n p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n,
    p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_and_inv {n p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋏[n] p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r = c.and param n p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
    ⟨_, _, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
  · simp [qqAnd, qqRel] at H
  · simp [qqAnd, qqNRel] at H
  · simp [qqAnd, qqVerum] at H
  · simp [qqAnd, qqFalsum] at H
  · simp [qqAnd, qqAnd] at H; rcases H with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqAnd, qqOr] at H
  · simp [qqAnd, qqAll] at H
  · simp [qqAnd, qqEx] at H

lemma graph_or {n p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsSemiformula n p₁) (hp₂ : L.IsSemiformula n p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋎[n] p₂) (c.or param n p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n,
    p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_or_inv {n p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋎[n] p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r = c.or param n p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
    ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩)⟩
  · simp [qqOr, qqRel] at H
  · simp [qqOr, qqNRel] at H
  · simp [qqOr, qqVerum] at H
  · simp [qqOr, qqFalsum] at H
  · simp [qqOr, qqAnd] at H
  · simp [qqOr, qqOr] at H; rcases H with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqOr, qqAll] at H
  · simp [qqOr, qqEx] at H

lemma graph_all {n p₁ r₁ : V} (hp₁ : L.IsSemiformula (n + 1) p₁) (h₁ : c.Graph param p₁ r₁) :
    c.Graph param (^∀[n] p₁) (c.all param n p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n,
    p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_all_inv {n p₁ r : V} :
    c.Graph param (^∀[n] p₁) r → ∃ r₁, c.Graph param p₁ r₁ ∧ r = c.all param n p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
    ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, rfl⟩ | ⟨_, _, _, _, H, _⟩)⟩
  · simp [qqAll, qqRel] at H
  · simp [qqAll, qqNRel] at H
  · simp [qqAll, qqVerum] at H
  · simp [qqAll, qqFalsum] at H
  · simp [qqAll, qqAnd] at H
  · simp [qqAll, qqOr] at H
  · simp [qqAll, qqAll] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩
  · simp [qqAll, qqEx] at H

lemma graph_ex {n p₁ r₁ : V} (hp₁ : L.IsSemiformula (n + 1) p₁) (h₁ : c.Graph param p₁ r₁) :
    c.Graph param (^∃[n] p₁) (c.ex param n p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨n,
    p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_ex_inv {n p₁ r : V} :
    c.Graph param (^∃[n] p₁) r → ∃ r₁, c.Graph param p₁ r₁ ∧ r = c.ex param n p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, H, _⟩ | ⟨_, H, _⟩ |
    ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, H, _⟩ | ⟨_, _, _, _, H, rfl⟩)⟩
  · simp [qqEx, qqRel] at H
  · simp [qqEx, qqNRel] at H
  · simp [qqEx, qqVerum] at H
  · simp [qqEx, qqFalsum] at H
  · simp [qqEx, qqAnd] at H
  · simp [qqEx, qqOr] at H
  · simp [qqEx, qqAll] at H
  · simp [qqEx, qqEx] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩

variable (param)

lemma graph_exists {p : V} : L.IsUFormula p → ∃ r, c.Graph param p r := by
  apply Language.IsUFormula.induction 𝚺 (P := fun p ↦ ∃ r, c.Graph param p r)
    (by apply Definable.ex
        exact ⟨β.graph.rew <| Rew.embSubsts (#1 :> #0 :> fun x ↦ &(param x)), fun v ↦ by simp [c.eval_graphDef]⟩)
  case hrel =>
    intro n k r v hkr hv; exact ⟨c.rel param n k r v, c.graph_rel hkr hv⟩
  case hnrel =>
    intro n k r v hkr hv; exact ⟨c.nrel param n k r v, c.graph_nrel hkr hv⟩
  case hverum =>
    intro n; exact ⟨c.verum param n, c.graph_verum n⟩
  case hfalsum =>
    intro n; exact ⟨c.falsum param n, c.graph_falsum n⟩
  case hand =>
    rintro n p₁ p₂ hp₁ hp₂ ⟨r₁, h₁⟩ ⟨r₂, h₂⟩; exact ⟨c.and param n p₁ p₂ r₁ r₂, c.graph_and hp₁ hp₂ h₁ h₂⟩
  case hor =>
    rintro n p₁ p₂ hp₁ hp₂ ⟨r₁, h₁⟩ ⟨r₂, h₂⟩; exact ⟨c.or param n p₁ p₂ r₁ r₂, c.graph_or hp₁ hp₂ h₁ h₂⟩
  case hall =>
    rintro n p₁ hp₁ ⟨r₁, h₁⟩; exact ⟨c.all param n p₁ r₁, c.graph_all hp₁ h₁⟩
  case hex =>
    rintro n p₁ hp₁ ⟨r₁, h₁⟩; exact ⟨c.ex param n p₁ r₁, c.graph_ex hp₁ h₁⟩

lemma graph_unique {p : V} : L.IsUFormula p → ∀ r r', c.Graph param p r → c.Graph param p r' → r = r' := by
  apply Language.IsUFormula.induction 𝚷 (P := fun p ↦ ∀ {r r'}, c.Graph param p r → c.Graph param p r' → r = r')
    (by apply Definable.all
        apply Definable.all
        apply Definable.imp
        · exact ⟨β.graph.rew <| Rew.embSubsts (#2 :> #1 :> fun x ↦ &(param x)), fun v ↦ by simp [c.eval_graphDef]⟩
        apply Definable.imp
        · exact ⟨β.graph.rew <| Rew.embSubsts (#2 :> #0 :> fun x ↦ &(param x)), fun v ↦ by simp [c.eval_graphDef]⟩
        definability)
  case hrel =>
    intro n k R v hkR hv
    simp [c.graph_rel_iff hkR hv]
  case hnrel =>
    intro n k R v hkR hv
    simp [c.graph_nrel_iff hkR hv]
  case hverum =>
    intro n; simp [c.graph_verum_iff]
  case hfalsum =>
    intro n; simp [c.graph_falsum_iff]
  case hand =>
    intro n p₁ p₂ _ _ ih₁ ih₂ r r' hr hr'
    rcases c.graph_and_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_and_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hor =>
    intro n p₁ p₂ _ _ ih₁ ih₂ r r' hr hr'
    rcases c.graph_or_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_or_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hall =>
    intro n p _ ih r r' hr hr'
    rcases c.graph_all_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_all_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl
  case hex =>
    intro n p _ ih r r' hr hr'
    rcases c.graph_ex_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_ex_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl

lemma exists_unique {p : V} (hp : L.IsUFormula p) : ∃! r, c.Graph param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique param hp r' r hr' hr)

lemma exists_unique_all (p : V) : ∃! r, (L.IsUFormula p → c.Graph param p r) ∧ (¬L.IsUFormula p → r = 0) := by
  by_cases hp : L.IsUFormula p <;> simp [hp, exists_unique]

def result (p : V) : V := Classical.choose! (c.exists_unique_all param p)

lemma result_prop {p : V} (hp : L.IsUFormula p) : c.Graph param p (c.result param p) :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬L.IsUFormula p) : c.result param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph param p r) : c.result param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all param p) (by simp [c.graph_dom_isUFormula h, h])

@[simp] lemma result_rel {n k R v} (hR : L.Rel k R) (hv : L.TermSeq k n v) :
    c.result param (^rel n k R v) = c.rel param n k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {n k R v} (hR : L.Rel k R) (hv : L.TermSeq k n v) :
    c.result param (^nrel n k R v) = c.nrel param n k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum {n} : c.result param ^⊤[n] = c.verum param n := c.result_eq_of_graph (c.graph_verum n)

@[simp] lemma result_falsum {n} : c.result param ^⊥[n] = c.falsum param n := c.result_eq_of_graph (c.graph_falsum n)

@[simp] lemma result_and {n p q}
    (hp : L.IsSemiformula n p) (hq : L.IsSemiformula n q) :
    c.result param (p ^⋏[n] q) = c.and param n p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp.1) (c.result_prop param hq.1))

@[simp] lemma result_or {n p q}
    (hp : L.IsSemiformula n p) (hq : L.IsSemiformula n q) :
    c.result param (p ^⋎[n] q) = c.or param n p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp.1) (c.result_prop param hq.1))

@[simp] lemma result_all {n p} (hp : L.IsSemiformula (n + 1) p) :
    c.result param (^∀[n] p) = c.all param n p (c.result param p) :=
  c.result_eq_of_graph (c.graph_all hp (c.result_prop param hp.1))

@[simp] lemma result_ex {n p} (hp : L.IsSemiformula (n + 1) p) :
    c.result param (^∃[n] p) = c.ex param n p (c.result param p) :=
  c.result_eq_of_graph (c.graph_ex hp (c.result_prop param hp.1))

section

lemma result_defined : Arith.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.result := by
  intro v
  simp [Blueprint.result, HSemiformula.val_sigma, eval_isUFormulaDef L, (isUFormula_defined L).proper.iff', c.eval_graphDef]
  exact Classical.choose!_eq_iff (c.exists_unique_all (v ·.succ.succ) (v 1))

end

end Construction

end Language.UformulaRec

namespace Negation

def blueprint (pL : LDef) : Language.UformulaRec.Blueprint pL 0 where
  rel := .mkSigma “y n k R v | !qqNRelDef y n k R v” (by simp)
  nrel := .mkSigma “y n k R v | !qqRelDef y n k R v” (by simp)
  verum := .mkSigma “y n | !qqFalsumDef y n” (by simp)
  falsum := .mkSigma “y n | !qqVerumDef y n” (by simp)
  and := .mkSigma “y n p₁ p₂ y₁ y₂ | !qqOrDef y n y₁ y₂” (by simp)
  or := .mkSigma “y n p₁ p₂ y₁ y₂ | !qqAndDef y n y₁ y₂” (by simp)
  all := .mkSigma “y n p₁ y₁ | !qqExDef y n y₁” (by simp)
  ex := .mkSigma “y n p₁ y₁ | !qqAllDef y n y₁” (by simp)

variable (L)

def construction : Language.UformulaRec.Construction V L (blueprint pL) where
  rel {_} := fun n k R v ↦ ^nrel n k R v
  nrel {_} := fun n k R v ↦ ^rel n k R v
  verum {_} := fun n ↦ ^⊥[n]
  falsum {_} := fun n ↦ ^⊤[n]
  and {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[n] y₂
  or {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[n] y₂
  all {_} := fun n _ y₁ ↦ ^∃[n] y₁
  ex {_} := fun n _ y₁ ↦ ^∀[n] y₁
  rel_defined := by intro v; simp [blueprint]; rfl
  nrel_defined := by intro v; simp [blueprint]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl

end Negation

section negation

open Negation

variable (L)

def Language.neg (p : V) : V := (construction L).result ![] p

variable {L}

@[simp] lemma neg_rel {n k R v} (hR : L.Rel k R) (hv : L.TermSeq k n v) :
    L.neg (^rel n k R v) = ^nrel n k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_nrel {n k R v} (hR : L.Rel k R) (hv : L.TermSeq k n v) :
    L.neg (^nrel n k R v) = ^rel n k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_verum (n) :
    L.neg ^⊤[n] = ^⊥[n] := by simp [Language.neg, construction]

@[simp] lemma neg_falsum (n) :
    L.neg ^⊥[n] = ^⊤[n] := by simp [Language.neg, construction]

@[simp] lemma neg_and {n p q} (hp : L.IsSemiformula n p) (hq : L.IsSemiformula n q) :
    L.neg (p ^⋏[n] q) = L.neg p ^⋎[n] L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_or {n p q} (hp : L.IsSemiformula n p) (hq : L.IsSemiformula n q) :
    L.neg (p ^⋎[n] q) = L.neg p ^⋏[n] L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_all {n p} (hp : L.IsSemiformula (n + 1) p) :
    L.neg (^∀[n] p) = ^∃[n] (L.neg p) := by simp [Language.neg, hp, construction]

@[simp] lemma neg_ex {n p} (hp : L.IsSemiformula (n + 1) p) :
    L.neg (^∃[n] p) = ^∀[n] (L.neg p) := by simp [Language.neg, hp, construction]

section

def _root_.LO.FirstOrder.Arith.LDef.negDef (pL : LDef) : 𝚺₁-Semisentence 2 := (blueprint pL).result

variable (L)

lemma neg_defined : 𝚺₁-Function₁ L.neg via pL.negDef := (construction L).result_defined

@[simp] lemma neg_defined_iff (v : Fin 2 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.negDef ↔ v 0 = L.neg (v 1) := (neg_defined L).df.iff v

instance neg_definable : 𝚺₁-Function₁ L.neg :=
  Defined.to_definable _ (neg_defined L)

@[simp, definability] instance neg_definable' (Γ) : (Γ, m + 1)-Function₁ L.neg :=
  .of_sigmaOne (neg_definable L) _ _

end

end negation

section substs

end substs

end LO.Arith

end
