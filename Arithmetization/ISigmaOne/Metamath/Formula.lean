import Arithmetization.ISigmaOne.Metamath.Term
import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

variable {L : Model.Language M} {pL : LDef} [Model.Language.Defined L pL]

section blueprint

def qqRel (n k r v : M) : M := ⟪n, 0, k, r, v⟫ + 1

def qqNRel (n k r v : M) : M := ⟪n, 1, k, r, v⟫ + 1

def qqVerum (n : M) : M := ⟪n, 2, 0⟫ + 1

def qqFalsum (n : M) : M := ⟪n, 3, 0⟫ + 1

def qqAnd (n p q : M) : M := ⟪n, 4, p, q⟫ + 1

def qqOr (n p q : M) : M := ⟪n, 5, p, q⟫ + 1

def qqForall (n p : M) : M := ⟪n, 6, p⟫ + 1

def qqExists (n p : M) : M := ⟪n, 7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤[" n "]" => qqVerum n

scoped notation "^⊥[" n "]" => qqFalsum n

scoped notation p:69 " ^⋏[" n "] " q:70 => qqAnd n p q

scoped notation p:68 " ^⋎[" n "] " q:69 => qqOr n p q

scoped notation "^∀[" n "] " p:64 => qqForall n p

scoped notation "^∃[" n "] " p:64 => qqExists n p

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

def _root_.LO.FirstOrder.Arith.qqForallDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “r n p | ∃ r' < r, !pair₃Def r' n 6 p ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqExistsDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “r n p | ∃ r' < r, !pair₃Def r' n 7 p ∧ r = r' + 1” (by simp)

lemma ss (x : M) : x < x + 1 := by exact lt_add_one x

lemma qqRel_defined : 𝚺₀-Function₄ (qqRel : M → M → M → M → M) via qqRelDef := by
  intro v; simp [qqRelDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqNRel_defined : 𝚺₀-Function₄ (qqNRel : M → M → M → M → M) via qqNRelDef := by
  intro v; simp [qqNRelDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqVerum_defined : 𝚺₀-Function₁ (qqVerum : M → M) via qqVerumDef := by
  intro v; simp [qqVerumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqFalsum_defined : 𝚺₀-Function₁ (qqFalsum : M → M) via qqFalsumDef := by
  intro v; simp [qqFalsumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqAnd_defined : 𝚺₀-Function₃ (qqAnd : M → M → M → M) via qqAndDef := by
  intro v; simp [qqAndDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqOr_defined : 𝚺₀-Function₃ (qqOr : M → M → M → M) via qqOrDef := by
  intro v; simp [qqOrDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqForall_defined : 𝚺₀-Function₂ (qqForall : M → M → M) via qqForallDef := by
  intro v; simp [qqForallDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqExists_defined : 𝚺₀-Function₂ (qqExists : M → M → M) via qqExistsDef := by
  intro v; simp [qqExistsDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_qqRelDef (v) :
    Semiformula.Evalbm M v qqRelDef.val ↔ v 0 = ^rel (v 1) (v 2) (v 3) (v 4) := qqRel_defined.df.iff v

@[simp] lemma eval_qqNRelDef (v) :
    Semiformula.Evalbm M v qqNRelDef.val ↔ v 0 = ^nrel (v 1) (v 2) (v 3) (v 4) := qqNRel_defined.df.iff v

@[simp] lemma eval_qqVerumDef (v) :
    Semiformula.Evalbm M v qqVerumDef.val ↔ v 0 = ^⊤[v 1] := qqVerum_defined.df.iff v

@[simp] lemma eval_qqFalsumDef (v) :
    Semiformula.Evalbm M v qqFalsumDef.val ↔ v 0 = ^⊥[v 1] := qqFalsum_defined.df.iff v

@[simp] lemma eval_qqAndDef (v) :
    Semiformula.Evalbm M v qqAndDef.val ↔ v 0 = (v 2) ^⋏[v 1] (v 3) := qqAnd_defined.df.iff v

@[simp] lemma eval_qqOrDef (v) :
    Semiformula.Evalbm M v qqOrDef.val ↔ v 0 = (v 2) ^⋎[v 1] (v 3) := qqOr_defined.df.iff v

@[simp] lemma eval_qqForallDef (v) :
    Semiformula.Evalbm M v qqForallDef.val ↔ v 0 = ^∀[v 1] (v 2) := qqForall_defined.df.iff v

@[simp] lemma eval_qqExistsDef (v) :
    Semiformula.Evalbm M v qqExistsDef.val ↔ v 0 = ^∃[v 1] (v 2) := qqExists_defined.df.iff v

def bv (p : M) : M := π₁ (p - 1)

def _root_.LO.FirstOrder.Arith.bvDef : 𝚺₀-Semisentence 2 :=
  .mkSigma “n p | ∃ p' <⁺ p, !subDef p' p 1 ∧ !pi₁Def n p'” (by simp)

lemma bv_defined : 𝚺₀-Function₁ (bv : M → M) via bvDef := by
  intro v; simp [bvDef]
  constructor
  · intro h; exact ⟨v 1 - 1, by simp, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_bvDef (v) :
    Semiformula.Evalbm M v bvDef.val ↔ v 0 = bv (v 1) := bv_defined.df.iff v

instance bv_definable : 𝚺₀-Function₁ (bv : M → M) := Defined.to_definable _ bv_defined

instance bv_definable' (Γ) : Γ-Function₁ (bv : M → M) := .of_zero bv_definable _

end

@[simp] lemma bv_lt_rel (n k r v : M) : n < ^rel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_rel (n k r v : M) : k < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_rel (n k r v : M) : r < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_rel (n k r v : M) : v < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_nrel (n k r v : M) : n < ^nrel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_nrel (n k r v : M) : k < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (n k r v : M) : r < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_nrel (n k r v : M) : v < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_verum (n : M) : n < ^⊤[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma bv_lt_falsum (n : M) : n < ^⊥[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma bv_lt_and (n p q : M) : n < p ^⋏[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_and_left (n p q : M) : p < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_and_right (n p q : M) : q < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_or (n p q : M) : n < p ^⋎[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_or_left (n p q : M) : p < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (n p q : M) : q < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_forall (n p : M) : n < ^∀[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_forall (n p : M) : p < ^∀[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma bv_lt_exists (n p : M) : n < ^∃[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_exists (n p : M) : p < ^∃[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

namespace FormalizedFormula

variable (L)

def Phi (C : Set M) (p : M) : Prop :=
  (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^rel n k r v) ∨
  (∃ n k r v, L.Rel k r ∧ L.TermSeq k n v ∧ p = ^nrel n k r v) ∨
  (∃ n, p = ^⊤[n]) ∨
  (∃ n, p = ^⊥[n]) ∨
  (∃ n q r, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋏[n] r) ∨
  (∃ n q r, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋎[n] r) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∀[n] q) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∃[n] q)

private lemma phi_iff (C p : M) :
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
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !bvDef (n + 1) q) ∧ !qqForallDef p n q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !bvDef (n + 1) q) ∧ !qqExistsDef p n q)”
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

def construction : Fixpoint.Construction M (blueprint pL) where
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
          Structure.Add.add, eval_qqForallDef, eval_qqExistsDef, LogicalConnective.Prop.or_eq] using
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

instance : (construction L).StrongFinite M where
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

open FormalizedFormula

variable (L)

def Language.IsUFormula : M → Prop := (construction L).Fixpoint ![]

def _root_.LO.FirstOrder.Arith.LDef.isUFormulaDef (pL : LDef) : 𝚫₁-Semisentence 1 :=
  (blueprint pL).fixpointDefΔ₁

lemma isUFormula_defined : 𝚫₁-Predicate L.IsUFormula via pL.isUFormulaDef :=
  (construction L).fixpoint_definedΔ₁

@[simp] lemma eval_isUFormulaDef (v) :
    Semiformula.Evalbm M v pL.isUFormulaDef.val ↔ L.IsUFormula (v 0) := (isUFormula_defined L).df.iff v

instance isUFormulaDef_definable : 𝚫₁-Predicate L.IsUFormula := Defined.to_definable _ (isUFormula_defined L)

@[simp, definability] instance isUFormulaDef_definable' (Γ) : (Γ, m + 1)-Predicate L.IsUFormula :=
  .of_deltaOne (isUFormulaDef_definable L) _ _

def Language.IsSemiformula (n p : M) : Prop := L.IsUFormula p ∧ bv p = n

def _root_.LO.FirstOrder.Arith.LDef.isSemiformulaDef (pL : LDef) : 𝚫₁-Semisentence 2 := .mkDelta
  (.mkSigma “n p | !pL.isUFormulaDef.sigma p ∧ !bvDef n p” (by simp))
  (.mkPi “n p | !pL.isUFormulaDef.pi p ∧ !bvDef n p” (by simp))

lemma isSemisentence_defined : 𝚫₁-Relation L.IsSemiformula via pL.isSemiformulaDef where
  left := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, (isUFormula_defined L).proper.iff']
  right := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, eval_isUFormulaDef L, Language.IsSemiformula, eq_comm]

variable {L}

local prefix:80 "𝐔 " => L.IsUFormula

lemma Language.IsUFormula.case_iff {p : M} :
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

@[simp] lemma Language.IsUFormula.rel {n k r v : M} :
    𝐔 (^rel n k r v) ↔ L.Rel k r ∧ L.TermSeq k n v :=
  ⟨by intro h
      rcases h.case with (⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.nrel {n k r v : M} :
    𝐔 (^nrel n k r v) ↔ L.Rel k r ∧ L.TermSeq k n v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.verum (n : M) : 𝐔 ^⊤[n] :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.IsUFormula.falsum (n : M) : 𝐔 ^⊥[n] :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.IsUFormula.and {n p q : M} :
    𝐔 (p ^⋏[n] q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, ⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.or {n p q : M} :
    𝐔 (p ^⋎[n] q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, ⟨hp.1, Eq.symm hp.2⟩, ⟨hq.1, Eq.symm hq.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.all {n p : M} :
    𝐔 (^∀[n] p) ↔ L.IsSemiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, hp, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp.1, Eq.symm hp.2⟩,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, p, ⟨hp.1, Eq.symm hp.2⟩, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.ex {n p : M} :
    𝐔 (^∃[n] p) ↔ L.IsSemiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqForall, qqExists] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp.1, Eq.symm hp.2⟩,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨n, p, ⟨hp.1, Eq.symm hp.2⟩, rfl⟩)⟩

lemma Language.IsUFormula.induction (Γ) {P : M → Prop} (hP : (Γ, 1)-Predicate P)
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

namespace Language.UformulaRec

structure Blueprint (k : ℕ) where
  rel : 𝚺₁-Semisentence (n + 5)
  nrel : 𝚺₁-Semisentence (n + 5)
  verum : 𝚺₁-Semisentence (n + 1)
  falsum : 𝚺₁-Semisentence (n + 1)
  and : 𝚺₁-Semisentence (n + 3)
  or : 𝚺₁-Semisentence (n + 3)
  all : 𝚺₁-Semisentence (n + 2)
  ex : 𝚺₁-Semisentence (n + 2)

variable (M)

structure Construction {k : ℕ} (φ : Blueprint k) where
  rel    : (Fin k → M) → M → M → M → M → M
  nrel   : (Fin k → M) → M → M → M → M → M
  verum  : (Fin k → M) → M → M
  falsum : (Fin k → M) → M → M
  and    : (Fin k → M) → M → M → M → M
  or     : (Fin k → M) → M → M → M → M
  all    : (Fin k → M) → M → M → M
  ex     : (Fin k → M) → M → M → M
  rel_defined    : DefinedFunction (fun v : Fin (k + 4) → M ↦ rel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.rel
  nrel_defined   : DefinedFunction (fun v : Fin (k + 4) → M ↦ rel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.nrel
  verum_defined  : DefinedFunction (fun v : Fin (k + 1) → M ↦ verum (v ·.succ) (v 0)) φ.verum
  falsum_defined : DefinedFunction (fun v : Fin (k + 1) → M ↦ falsum (v ·.succ) (v 0)) φ.verum
  and_defined    : DefinedFunction (fun v : Fin (k + 3) → M ↦ and (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.and
  or_defined     : DefinedFunction (fun v : Fin (k + 3) → M ↦ or  (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.or
  all_defined    : DefinedFunction (fun v : Fin (k + 2) → M ↦ all (v ·.succ.succ) (v 0) (v 1)) φ.all
  ex_defined     : DefinedFunction (fun v : Fin (k + 2) → M ↦ ex  (v ·.succ.succ) (v 0) (v 1)) φ.ex

variable {M}

namespace Construction

variable (L)

variable {β : Blueprint k} (c : Construction M β)

def Phi (param : Fin k → M) (C : Set M) (pr : M) : Prop :=
  L.IsUFormula (π₁ pr) ∧ (
  (∃ n k r v, pr = ⟪^rel n k r v, c.rel param n k r v⟫) ∨
  (∃ n k r v, pr = ⟪^nrel n k r v, c.nrel param n k r v⟫) ∨
  (∃ n, pr = ⟪^⊤[n], c.verum param n⟫) ∨
  (∃ n, pr = ⟪^⊥[n], c.verum param n⟫) ∨
  (∃ n p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪p ^⋏[n] q, c.and param n p' q'⟫) ∨
  (∃ n p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪p ^⋎[n] q, c.or param n p' q'⟫) ∨
  (∃ n p, pr = ⟪^∀[n] p, c.all param n p⟫) ∨
  (∃ n p, pr = ⟪^∃[n] p, c.ex param n p⟫) )

/-
private lemma phi_iff (param : Fin k → M) (C pr : M) :
    c.Phi L param {x | x ∈ C} pr ↔
    ∃ p r, pr = ⟪p, r⟫ ∧ L.IsUFormula p ∧
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, p = ^rel n k r v ∧ r = c.rel param n k r v) ∨
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, p = ^nrel n k r v) ∨
    (∃ n < p, p = ^⊤[n]) ∨
    (∃ n < p, p = ^⊥[n]) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋏[n] r) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = bv q) ∧ (r ∈ C ∧ n = bv r) ∧ p = q ^⋎[n] r) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∀[n] q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = bv q) ∧ p = ^∃[n] q) where
  mp := by

def fixpointBlueprint : Fixpoint.Blueprint k := ⟨.mkDelta
  (.mkSigma “p C |
    (∃ n < !β.rel)
  ” (by {  }))
  (by {  })
⟩

-/

end Construction

end Language.UformulaRec

end blueprint



end LO.FirstOrder.Arith.Model

end
