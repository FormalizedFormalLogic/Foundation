import Arithmetization.ISigmaOne.Metamath.Term.Basic

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

scoped notation "^⊤" => qqVerum 0

scoped notation "^⊥" => qqFalsum 0

scoped notation p:69 " ^⋏ " q:70 => qqAnd 0 p q

scoped notation p:68 " ^⋎ " q:69 => qqOr 0 p q

scoped notation "^∀ " p:64 => qqAll 0 p

scoped notation "^∃ " p:64 => qqEx 0 p

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

end

@[simp] lemma qqRel_inj (n₁ k₁ r₁ v₁ n₂ k₂ r₂ v₂ : V) :
    ^rel n₁ k₁ r₁ v₁ = ^rel n₂ k₂ r₂ v₂ ↔ n₁ = n₂ ∧ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqRel]
@[simp] lemma qqNRel_inj (n₁ k₁ r₁ v₁ n₂ k₂ r₂ v₂ : V) :
    ^nrel n₁ k₁ r₁ v₁ = ^nrel n₂ k₂ r₂ v₂ ↔ n₁ = n₂ ∧ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqNRel]
@[simp] lemma qqVerum_inj (n₁ n₂ : V) : ^⊤[n₁] = ^⊤[n₂] ↔ n₁ = n₂ := by simp [qqVerum]
@[simp] lemma qqFalsum_inj (n₁ n₂ : V) : ^⊥[n₁] = ^⊥[n₂] ↔ n₁ = n₂ := by simp [qqFalsum]
@[simp] lemma qqAnd_inj (n₁ p₁ q₁ n₂ p₂ q₂ : V) : p₁ ^⋏[n₁] q₁ = p₂ ^⋏[n₂] q₂ ↔ n₁ = n₂ ∧ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqAnd]
@[simp] lemma qqOr_inj (n₁ p₁ q₁ n₂ p₂ q₂ : V) : p₁ ^⋎[n₁] q₁ = p₂ ^⋎[n₂] q₂ ↔ n₁ = n₂ ∧ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqOr]
@[simp] lemma qqAll_inj (n₁ p₁ n₂ p₂ : V) : ^∀[n₁] p₁ = ^∀[n₂] p₂ ↔ n₁ = n₂ ∧ p₁ = p₂ := by simp [qqAll]
@[simp] lemma qqEx_inj (n₁ p₁ n₂ p₂ : V) : ^∃[n₁] p₁ = ^∃[n₂] p₂ ↔ n₁ = n₂ ∧ p₁ = p₂ := by simp [qqEx]

@[simp] lemma fstIdx_lt_rel (n k r v : V) : n < ^rel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_rel (n k r v : V) : k < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_rel (n k r v : V) : r < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_rel (n k r v : V) : v < ^rel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_lt_nrel (n k r v : V) : n < ^nrel n k r v := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_nrel (n k r v : V) : k < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (n k r v : V) : r < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_nrel (n k r v : V) : v < ^nrel n k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_lt_verum (n : V) : n < ^⊤[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma fstIdx_lt_falsum (n : V) : n < ^⊥[n] := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma fstIdx_lt_and (n p q : V) : n < p ^⋏[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_and_left (n p q : V) : p < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_and_right (n p q : V) : q < p ^⋏[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_lt_or (n p q : V) : n < p ^⋎[n] q := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_or_left (n p q : V) : p < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (n p q : V) : q < p ^⋎[n] q := le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_lt_forall (n p : V) : n < ^∀[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_forall (n p : V) : p < ^∀[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_lt_exists (n p : V) : n < ^∃[n] p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma lt_exists (n p : V) : p < ^∃[n] p := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_rel (n k r v : V) : fstIdx (^rel n k r v) = n := by simp [fstIdx, qqRel]
@[simp] lemma fstIdx_nrel (n k r v : V) : fstIdx (^nrel n k r v) = n := by simp [fstIdx, qqNRel]
@[simp] lemma fstIdx_verum (n : V) : fstIdx ^⊤[n] = n := by simp [fstIdx, qqVerum]
@[simp] lemma fstIdx_falsum (n : V) : fstIdx ^⊥[n] = n := by simp [fstIdx, qqFalsum]
@[simp] lemma fstIdx_and (n p q : V) : fstIdx (p ^⋏[n] q) = n := by simp [fstIdx, qqAnd]
@[simp] lemma fstIdx_or (n p q : V) : fstIdx (p ^⋎[n] q) = n := by simp [fstIdx, qqOr]
@[simp] lemma fstIdx_all (n p : V) : fstIdx (^∀[n] p) = n := by simp [fstIdx, qqAll]
@[simp] lemma fstIdx_ex (n p : V) : fstIdx (^∃[n] p) = n := by simp [fstIdx, qqEx]

namespace FormalizedFormula

variable (L)

def Phi (C : Set V) (p : V) : Prop :=
  (∃ n k r v, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^rel n k r v) ∨
  (∃ n k r v, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^nrel n k r v) ∨
  (∃ n, p = ^⊤[n]) ∨
  (∃ n, p = ^⊥[n]) ∨
  (∃ n q r, (q ∈ C ∧ n = fstIdx q) ∧ (r ∈ C ∧ n = fstIdx r) ∧ p = q ^⋏[n] r) ∨
  (∃ n q r, (q ∈ C ∧ n = fstIdx q) ∧ (r ∈ C ∧ n = fstIdx r) ∧ p = q ^⋎[n] r) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = fstIdx q) ∧ p = ^∀[n] q) ∨
  (∃ n q, (q ∈ C ∧ n + 1 = fstIdx q) ∧ p = ^∃[n] q)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^rel n k r v) ∨
    (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^nrel n k r v) ∨
    (∃ n < p, p = ^⊤[n]) ∨
    (∃ n < p, p = ^⊥[n]) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = fstIdx q) ∧ (r ∈ C ∧ n = fstIdx r) ∧ p = q ^⋏[n] r) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ n = fstIdx q) ∧ (r ∈ C ∧ n = fstIdx r) ∧ p = q ^⋎[n] r) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = fstIdx q) ∧ p = ^∀[n] q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ n + 1 = fstIdx q) ∧ p = ^∃[n] q) where
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
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ !fstIdxDef n q) ∧ (r ∈ C ∧ !fstIdxDef n r) ∧ !qqAndDef p n q r) ∨
    (∃ n < p, ∃ q < p, ∃ r < p, (q ∈ C ∧ !fstIdxDef n q) ∧ (r ∈ C ∧ !fstIdxDef n r) ∧ !qqOrDef p n q r) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !fstIdxDef (n + 1) q) ∧ !qqAllDef p n q) ∨
    (∃ n < p, ∃ q < p, (q ∈ C ∧ !fstIdxDef (n + 1) q) ∧ !qqExDef p n q)”
  (by simp)

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma
    “p C |
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.semitermVecDef.sigma k n v ∧ !qqRelDef p n k r v) ∨
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.semitermVecDef.sigma k n v ∧ !qqNRelDef p n k r v) ∨
      !formulaAux p C” (by simp))
  (.mkPi
    “p C |
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.semitermVecDef.pi k n v ∧ !qqRelDef p n k r v) ∨
      (∃ n < p, ∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.semitermVecDef.pi k n v ∧ !qqNRelDef p n k r v) ∨
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
          (semitermVec_defined L).proper.iff'],
    by  intro v
        -- simpa [blueprint, Language.Defined.eval_rel_iff (L := L), eval_termSeq L, HSemiformula.val_sigma, formulaAux] using phi_iff L _ _
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
          HSemiformula.val_sigma, formulaAux, HSemiformula.val_mkSigma,
          LogicalConnective.HomClass.map_or, HSemiformula.val_mkDelta, Semiformula.eval_bexLT,
          Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two,
          Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_three,
          Fin.succ_one_eq_two, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
          Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
          Matrix.constant_eq_singleton, Language.Defined.eval_rel_iff (L := L), (semitermVec_defined L).df.iff,
          Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, eval_qqVerumDef, eval_qqFalsumDef, Semiformula.eval_operator₂,
          Structure.Mem.mem, eval_fstIdxDef, eval_qqAndDef, eval_qqOrDef, Semiterm.val_operator₂,
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

def Language.UFormula : V → Prop := (construction L).Fixpoint ![]

def _root_.LO.FirstOrder.Arith.LDef.uformulaDef (pL : LDef) : 𝚫₁-Semisentence 1 :=
  (blueprint pL).fixpointDefΔ₁

lemma uformula_defined : 𝚫₁-Predicate L.UFormula via pL.uformulaDef :=
  (construction L).fixpoint_definedΔ₁

@[simp] lemma eval_uformulaDef (v) :
    Semiformula.Evalbm V v pL.uformulaDef.val ↔ L.UFormula (v 0) := (uformula_defined L).df.iff v

instance uformulaDef_definable : 𝚫₁-Predicate L.UFormula := Defined.to_definable _ (uformula_defined L)

@[simp, definability] instance uformulaDef_definable' (Γ) : (Γ, m + 1)-Predicate L.UFormula :=
  .of_deltaOne (uformulaDef_definable L) _ _

def Language.Semiformula (n p : V) : Prop := L.UFormula p ∧ n = fstIdx p

abbrev Language.Formula (p : V) : Prop := L.Semiformula 0 p

lemma Language.UFormula.toSemiformula {p} (h : L.UFormula p) : L.Semiformula (fstIdx p) p :=
  ⟨h, by rfl⟩

def _root_.LO.FirstOrder.Arith.LDef.isSemiformulaDef (pL : LDef) : 𝚫₁-Semisentence 2 := .mkDelta
  (.mkSigma “n p | !pL.uformulaDef.sigma p ∧ !fstIdxDef n p” (by simp))
  (.mkPi “n p | !pL.uformulaDef.pi p ∧ !fstIdxDef n p” (by simp))

lemma semiformula_defined : 𝚫₁-Relation L.Semiformula via pL.isSemiformulaDef where
  left := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, (uformula_defined L).proper.iff']
  right := by intro v; simp [LDef.isSemiformulaDef, HSemiformula.val_sigma, eval_uformulaDef L, Language.Semiformula, eq_comm]

instance semiformula_definable : 𝚫₁-Relation L.Semiformula := Defined.to_definable _ (semiformula_defined L)

@[simp, definability] instance semiformula_defined' (Γ) : (Γ, m + 1)-Relation L.Semiformula :=
  .of_deltaOne (semiformula_definable L) _ _

variable {L}

local prefix:80 "𝐔 " => L.UFormula

lemma Language.UFormula.case_iff {p : V} :
    𝐔 p ↔
    (∃ n k r v, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^rel n k r v) ∨
    (∃ n k r v, L.Rel k r ∧ L.SemitermVec k n v ∧ p = ^nrel n k r v) ∨
    (∃ n, p = ^⊤[n]) ∨
    (∃ n, p = ^⊥[n]) ∨
    (∃ n q r, L.Semiformula n q ∧ L.Semiformula n r ∧ p = q ^⋏[n] r) ∨
    (∃ n q r, L.Semiformula n q ∧ L.Semiformula n r ∧ p = q ^⋎[n] r) ∨
    (∃ n q, L.Semiformula (n + 1) q ∧ p = ^∀[n] q) ∨
    (∃ n q, L.Semiformula (n + 1) q ∧ p = ^∃[n] q) :=
  (construction L).case

alias ⟨Language.UFormula.case, Language.UFormula.mk⟩ := Language.UFormula.case_iff

@[simp] lemma Language.UFormula.rel {n k r v : V} :
    𝐔 (^rel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v :=
  ⟨by intro h
      rcases h.case with (⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.UFormula.mk (Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.UFormula.nrel {n k r v : V} :
    𝐔 (^nrel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨n, k, r, v, hkr, hv, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.UFormula.mk (Or.inr <| Or.inl ⟨n, k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.UFormula.verum (n : V) : 𝐔 ^⊤[n] :=
  Language.UFormula.mk (Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.UFormula.falsum (n : V) : 𝐔 ^⊥[n] :=
  Language.UFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl⟩)

@[simp] lemma Language.UFormula.and {n p q : V} :
    𝐔 (p ^⋏[n] q) ↔ L.Semiformula n p ∧ L.Semiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact Language.UFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, hp, hq, rfl⟩)⟩

@[simp] lemma Language.UFormula.or {n p q : V} :
    𝐔 (p ^⋎[n] q) ↔ L.Semiformula n p ∧ L.Semiformula n q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, hp, hq, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact Language.UFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨n, p, q, hp, hq, rfl⟩)⟩

@[simp] lemma Language.UFormula.all {n p : V} :
    𝐔 (^∀[n] p) ↔ L.Semiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, hp, h⟩ | ⟨_, _, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact Language.UFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, p, hp, rfl⟩)⟩

@[simp] lemma Language.UFormula.ex {n p : V} :
    𝐔 (^∃[n] p) ↔ L.Semiformula (n + 1) p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact Language.UFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨n, p, hp, rfl⟩)⟩

lemma Language.UFormula.pos {p : V} (h : L.UFormula p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]

lemma Language.Semiformula.pos {n p : V} (h : L.Semiformula n p) : 0 < p := h.1.pos

@[simp] lemma Language.UFormula.not_zero : ¬L.UFormula (0 : V) := by intro h; simpa using h.pos

@[simp] lemma Language.Semiformula.not_zero (m : V) : ¬L.Semiformula m (0 : V) := by intro h; simpa using h.pos

@[simp] lemma Language.Semiformula.rel {n k r v : V} :
    L.Semiformula n (^rel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.nrel {n k r v : V} :
    L.Semiformula n (^nrel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.verum (n : V) : L.Semiformula n ^⊤[n] := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.falsum (n : V) : L.Semiformula n ^⊥[n] := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.and {n p q : V} :
    L.Semiformula n (p ^⋏[n] q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.or {n p q : V} :
    L.Semiformula n (p ^⋎[n] q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.all {n p : V} : L.Semiformula n (^∀[n] p) ↔ L.Semiformula (n + 1) p := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.ex {n p : V} : L.Semiformula n (^∃[n] p) ↔ L.Semiformula (n + 1) p := by simp [Language.Semiformula]

lemma Language.UFormula.induction (Γ) {P : V → Prop} (hP : (Γ, 1)-Predicate P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P (^nrel n k r v))
    (hverum : ∀ n, P ^⊤[n])
    (hfalsum : ∀ n, P ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P p → P q → P (p ^⋏[n] q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P p → P q → P (p ^⋎[n] q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P p → P (^∀[n] p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P p → P (^∃[n] p)) :
    ∀ p, 𝐔 p → P p :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
      ⟨n, p, q, ⟨hp, hnp⟩, ⟨hq, hnq⟩, rfl⟩ | ⟨n, p, q, ⟨hp, hnp⟩, ⟨hq, hnq⟩, rfl⟩ | ⟨n, p, ⟨hp, hnp⟩, rfl⟩ | ⟨n, p, ⟨hp, hnp⟩, rfl⟩)
    · exact hrel n k r v hkr hv
    · exact hnrel n k r v hkr hv
    · exact hverum n
    · exact hfalsum n
    · exact hand n p q ⟨(hC p hp).1, hnp⟩ ⟨(hC q hq).1, hnq⟩ (hC p hp).2 (hC q hq).2
    · exact hor n p q ⟨(hC p hp).1, hnp⟩ ⟨(hC q hq).1, hnq⟩ (hC p hp).2 (hC q hq).2
    · exact hall n p ⟨(hC p hp).1, hnp⟩ (hC p hp).2
    · exact hex n p ⟨(hC p hp).1, hnp⟩ (hC p hp).2)

lemma Language.Semiformula.induction (Γ) {P : V → V → Prop} (hP : (Γ, 1)-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏[n] q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎[n] q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀[n] p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃[n] p)) :
    ∀ n p, L.Semiformula n p → P n p := by
  suffices ∀ p, 𝐔 p → ∀ n ≤ p, fstIdx p = n → P n p
  by rintro n p ⟨h, rfl⟩; exact this p h (fstIdx p) (by simp) rfl
  apply Language.UFormula.induction (P := fun p ↦ ∀ n ≤ p, fstIdx p = n → P n p) Γ
  · apply Definable.ball_le (by definability)
    apply Definable.imp (by definability)
    simp; exact hP
  · rintro n k r v hr hv _ _ rfl; simpa using hrel n k r v hr hv
  · rintro n k r v hr hv _ _ rfl; simpa using hnrel n k r v hr hv
  · rintro n _ _ rfl; simpa using hverum n
  · rintro n _ _ rfl; simpa using hfalsum n
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hand n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hor n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hall n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hex n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)

lemma Language.Semiformula.induction_sigma₁ {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏[n] q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎[n] q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀[n] p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃[n] p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.Semiformula.induction 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hex

lemma Language.Semiformula.induction_pi₁ {P : V → V → Prop} (hP : 𝚷₁-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏[n] q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎[n] q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀[n] p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃[n] p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.Semiformula.induction 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hex

end formula

namespace Language.UformulaRec1

structure Blueprint (pL : LDef) where
  rel        : 𝚺₁-Semisentence 6
  nrel       : 𝚺₁-Semisentence 6
  verum      : 𝚺₁-Semisentence 3
  falsum     : 𝚺₁-Semisentence 3
  and        : 𝚺₁-Semisentence 7
  or         : 𝚺₁-Semisentence 7
  all        : 𝚺₁-Semisentence 5
  ex         : 𝚺₁-Semisentence 5
  allChanges : 𝚺₁-Semisentence 3
  exChanges  : 𝚺₁-Semisentence 3

namespace Blueprint

variable {pL : LDef} (β : Blueprint pL)

def blueprint (β : Blueprint pL) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C |
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.uformulaDef.sigma p ∧
    ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p n k R v ∧ !β.rel y param n k R v) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p n k R v ∧ !β.nrel y param n k R v) ∨
    (∃ n < p, !qqVerumDef p n ∧ !β.verum y param n) ∨
    (∃ n < p, !qqFalsumDef p n ∧ !β.falsum y param n) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p n p₁ p₂ ∧ !β.and y param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p n p₁ p₂ ∧ !β.or y param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.allChanges param' param n ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p n p₁ ∧ !β.all y param n p₁ y₁) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.exChanges param' param n ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p n p₁ ∧ !β.ex y param n p₁ y₁))
  ” (by simp))
  (.mkPi “pr C |
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.uformulaDef.pi p ∧
    ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p n k R v ∧ !β.rel.graphDelta.pi.val y param n k R v) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p n k R v ∧ !β.nrel.graphDelta.pi.val y param n k R v) ∨
    (∃ n < p, !qqVerumDef p n ∧ !β.verum.graphDelta.pi.val y param n) ∨
    (∃ n < p, !qqFalsumDef p n ∧ !β.falsum.graphDelta.pi.val y param n) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p n p₁ p₂ ∧ !β.and.graphDelta.pi.val y param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p n p₁ p₂ ∧ !β.or.graphDelta.pi.val y param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.allChanges param' param n → :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p n p₁ ∧ !β.all.graphDelta.pi.val y param n p₁ y₁) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.exChanges param' param n → :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p n p₁ ∧ !β.ex.graphDelta.pi.val y param n p₁ y₁))
  ” (by simp))⟩

def graph : 𝚺₁-Semisentence 3 := .mkSigma
  “param p y | ∃ pr, !pair₃Def pr param p y ∧ !β.blueprint.fixpointDef pr” (by simp)

def result : 𝚺₁-Semisentence 3 := .mkSigma
  “y param p | (!pL.uformulaDef.pi p → !β.graph param p y) ∧ (¬!pL.uformulaDef.sigma p → y = 0)” (by simp)

end Blueprint

variable (V)

structure Construction (L : Arith.Language V) (φ : Blueprint pL) where
  rel        (param n k R v : V) : V
  nrel       (param n k R v : V) : V
  verum      (param n : V) : V
  falsum     (param n : V) : V
  and        (param n p₁ p₂ y₁ y₂ : V) : V
  or         (param n p₁ p₂ y₁ y₂ : V) : V
  all        (param n p₁ y₁ : V) : V
  ex         (param n p₁ y₁ : V) : V
  allChanges (param n : V) : V
  exChanges  (param n : V) : V
  rel_defined    : DefinedFunction (fun v ↦ rel (v 0) (v 1) (v 2) (v 3) (v 4)) φ.rel
  nrel_defined   : DefinedFunction (fun v ↦ nrel (v 0) (v 1) (v 2) (v 3) (v 4)) φ.nrel
  verum_defined  : DefinedFunction (fun v ↦ verum (v 0) (v 1)) φ.verum
  falsum_defined : DefinedFunction (fun v ↦ falsum (v 0) (v 1)) φ.falsum
  and_defined    : DefinedFunction (fun v ↦ and (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) φ.and
  or_defined     : DefinedFunction (fun v ↦ or  (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) φ.or
  all_defined    : DefinedFunction (fun v ↦ all (v 0) (v 1) (v 2) (v 3)) φ.all
  ex_defined     : DefinedFunction (fun v ↦ ex  (v 0) (v 1) (v 2) (v 3)) φ.ex
  allChanges_defined : 𝚺₁-Function₂ allChanges via φ.allChanges
  exChanges_defined  : 𝚺₁-Function₂ exChanges via φ.exChanges

variable {V}

namespace Construction

variable {β : Blueprint pL} (c : Construction V L β)

def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧
  L.UFormula p ∧ (
  (∃ n k r v, p = ^rel n k r v ∧ y = c.rel param n k r v) ∨
  (∃ n k r v, p = ^nrel n k r v ∧ y = c.nrel param n k r v) ∨
  (∃ n, p = ^⊤[n] ∧ y = c.verum param n) ∨
  (∃ n, p = ^⊥[n] ∧ y = c.falsum param n) ∨
  (∃ n p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏[n] p₂ ∧ y = c.and param n p₁ p₂ y₁ y₂) ∨
  (∃ n p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎[n] p₂ ∧ y = c.or  param n p₁ p₂ y₁ y₂) ∨
  (∃ n p₁ y₁, ⟪c.allChanges param n, p₁, y₁⟫ ∈ C ∧ p = ^∀[n] p₁ ∧ y = c.all param n p₁ y₁) ∨
  (∃ n p₁ y₁, ⟪c.exChanges param n, p₁, y₁⟫ ∈ C ∧ p = ^∃[n] p₁ ∧ y = c.ex  param n p₁ y₁) )

private lemma phi_iff (C pr : V) :
    c.Phi {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ L.UFormula p ∧
    ((∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, p = ^rel n k R v ∧ y = c.rel param n k R v) ∨
    (∃ n < p, ∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel n k R v ∧ y = c.nrel param n k R v) ∨
    (∃ n < p, p = ^⊤[n] ∧ y = c.verum param n) ∨
    (∃ n < p, p = ^⊥[n] ∧ y = c.falsum param n) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏[n] p₂ ∧ y = c.and param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎[n] p₂ ∧ y = c.or param n p₁ p₂ y₁ y₂) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      ⟪c.allChanges param n, p₁, y₁⟫ ∈ C ∧ p = ^∀[n] p₁ ∧ y = c.all param n p₁ y₁) ∨
    (∃ n < p, ∃ p₁ < p, ∃ y₁ < C,
      ⟪c.exChanges param n, p₁, y₁⟫ ∈ C ∧ p = ^∃[n] p₁ ∧ y = c.ex param n p₁ y₁)) := by
  constructor
  · rintro ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, by simp,
      p, le_trans (le_pair_left p y) (le_pair_right _ _),
      y, le_trans (le_pair_right p y) (le_pair_right _ _), rfl, hp, ?_⟩
    rcases H with (⟨n, k, r, v, rfl, rfl⟩ | ⟨n, k, r, v, rfl, rfl⟩ | H)
    · left; exact ⟨n, by simp, k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    · right; left; exact ⟨n, by simp, k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    right; right
    rcases H with (⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | H)
    · left; exact ⟨n, by simp, rfl, rfl⟩
    · right; left; exact ⟨n, by simp, rfl, rfl⟩
    right; right
    rcases H with (⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨n, by simp, p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨n, by simp, p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨n, p₁, y₁, h₁, rfl, rfl⟩ | ⟨n, p₁, y₁, h₁, rfl, rfl⟩)
    · left; exact ⟨n, by simp, p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
    · right; exact ⟨n, by simp, p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
  · rintro ⟨param, _, p, _, y, _, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (⟨n, _, k, _, r, _, v, _, rfl, rfl⟩ | ⟨n, _, k, _, r, _, v, _, rfl, rfl⟩ | H)
    · left; exact ⟨n, k, r, v, rfl, rfl⟩
    · right; left; exact ⟨n, k, r, v, rfl, rfl⟩
    right; right
    rcases H with (⟨n, _, rfl, rfl⟩ | ⟨n, _, rfl, rfl⟩ | H)
    · left; exact ⟨n, rfl, rfl⟩
    · right; left; exact ⟨n, rfl, rfl⟩
    right; right
    rcases H with (⟨n, _, p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨n, _, p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨n, _, p₁, _, y₁, _, h₁, rfl, rfl⟩ | ⟨n, _, p₁, _, y₁, _, h₁, rfl, rfl⟩)
    · left; exact ⟨n, p₁, y₁, h₁, rfl, rfl⟩
    · right; exact ⟨n, p₁, y₁, h₁, rfl, rfl⟩

def construction : Fixpoint.Construction V (β.blueprint) where
  Φ := fun _ ↦ c.Phi
  defined :=
  ⟨by intro v
      /-
      simp? [HSemiformula.val_sigma, Blueprint.blueprint,
        eval_uformulaDef L, (uformula_defined L).proper.iff',
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.ex_defined.iff, c.ex_defined.graph_delta.proper.iff',
        c.allChanges_defined.iff, c.allChanges_defined.graph_delta.proper.iff',
        c.exChanges_defined.iff, c.exChanges_defined.graph_delta.proper.iff']
      -/
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint, Fin.isValue,
        HSemiformula.val_sigma, HSemiformula.sigma_mkDelta, HSemiformula.val_mkSigma,
        Semiformula.eval_bexLTSucc', Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
        LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
        Matrix.cons_val_three, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.constant_eq_singleton, eval_pair₃Def, eval_uformulaDef L,
        LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Matrix.cons_val_four,
        Matrix.cons_val_succ, Matrix.cons_app_five, eval_qqRelDef, Matrix.cons_app_six,
        c.rel_defined.iff, LogicalConnective.Prop.and_eq, c.nrel_defined.iff, eval_qqVerumDef,
        c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff, Matrix.cons_app_seven,
        Matrix.cons_app_eight, Semiformula.eval_operator₄, TermRec.Construction.cons_app_9,
        eval_memRel₃, eval_qqAndDef, c.and_defined.iff, eval_qqOrDef, c.or_defined.iff,
        Semiformula.eval_ex, c.allChanges_defined.iff, exists_eq_left, eval_qqAllDef,
        c.all_defined.iff, c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
        LogicalConnective.Prop.or_eq, HSemiformula.pi_mkDelta, HSemiformula.val_mkPi,
        (uformula_defined L).proper.iff', c.rel_defined.graph_delta.proper.iff',
        HSemiformula.graphDelta_val, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.graph_delta.proper.iff', c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.graph_delta.proper.iff', c.or_defined.graph_delta.proper.iff',
        Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
        forall_eq, c.all_defined.graph_delta.proper.iff', c.ex_defined.graph_delta.proper.iff'],
    by  intro v
        /-
        simpa [HSemiformula.val_sigma, Blueprint.blueprint,
          eval_uformulaDef L,
          c.rel_defined.iff,
          c.nrel_defined.iff,
          c.verum_defined.iff,
          c.falsum_defined.iff,
          c.and_defined.iff,
          c.or_defined.iff,
          c.all_defined.iff,
          c.ex_defined.iff,
          c.allChanges_defined.iff,
          c.exChanges_defined.iff] using c.phi_iff _ _
        -/
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint,
          HSemiformula.val_sigma, HSemiformula.val_mkDelta, HSemiformula.val_mkSigma,
          Semiformula.eval_bexLTSucc', Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
          Matrix.cons_val_three, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
          Matrix.constant_eq_singleton, eval_pair₃Def, eval_uformulaDef L,
          LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, Matrix.cons_val_four,
          Matrix.cons_val_succ, Matrix.cons_app_five, eval_qqRelDef, Matrix.cons_app_six,
          c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef, c.nrel_defined.iff,
          eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff,
          Matrix.cons_app_seven, Matrix.cons_app_eight, Semiformula.eval_operator₄,
          TermRec.Construction.cons_app_9, eval_memRel₃, eval_qqAndDef, c.and_defined.iff,
          eval_qqOrDef, c.or_defined.iff, Semiformula.eval_ex, c.allChanges_defined.iff,
          exists_eq_left, eval_qqAllDef, c.all_defined.iff, c.exChanges_defined.iff, eval_qqExDef,
          c.ex_defined.iff, LogicalConnective.Prop.or_eq] using c.phi_iff _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ _ ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | ⟨n, p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨n, p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    · right; left; exact ⟨n, p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨n, p₁, r₁, h₁, rfl, rfl⟩ | ⟨n, p₁, r₁, h₁, rfl, rfl⟩)
    · left; exact ⟨n, p₁, r₁, hC h₁, rfl, rfl⟩
    · right; exact ⟨n, p₁, r₁, hC h₁, rfl, rfl⟩

instance : c.construction.Finite where
  finite {C _ pr h} := by
    rcases h with ⟨param, p, y, rfl, hp, (h | h | h | h |
      ⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨n, p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨n, p₁, y₁, h₁, rfl, rfl⟩ | ⟨n, p₁, y₁, h₁, rfl, rfl⟩)⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; left
        exact ⟨n, p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl, rfl⟩⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; left
        exact ⟨n, p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl, rfl⟩⟩
    · exact ⟨⟪c.allChanges param n, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; left
        exact ⟨n, p₁, y₁, by simp [h₁], rfl, rfl⟩⟩
    · exact ⟨⟪c.exChanges param n, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; right
        exact ⟨n, p₁, y₁, by simp [h₁], rfl, rfl⟩⟩

def Graph (param : V) (x y : V) : Prop := c.construction.Fixpoint ![] ⟪param, x, y⟫

variable {param : V}

variable {c}

lemma Graph.case_iff {p y : V} :
    c.Graph param p y ↔
    L.UFormula p ∧ (
    (∃ n k R v, p = ^rel n k R v ∧ y = c.rel param n k R v) ∨
    (∃ n k R v, p = ^nrel n k R v ∧ y = c.nrel param n k R v) ∨
    (∃ n, p = ^⊤[n] ∧ y = c.verum param n) ∨
    (∃ n, p = ^⊥[n] ∧ y = c.falsum param n) ∨
    (∃ n p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋏[n] p₂ ∧ y = c.and param n p₁ p₂ y₁ y₂) ∨
    (∃ n p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋎[n] p₂ ∧ y = c.or param n p₁ p₂ y₁ y₂) ∨
    (∃ n p₁ y₁, c.Graph (c.allChanges param n) p₁ y₁ ∧ p = ^∀[n] p₁ ∧ y = c.all param n p₁ y₁) ∨
    (∃ n p₁ y₁, c.Graph (c.exChanges param n) p₁ y₁ ∧ p = ^∃[n] p₁ ∧ y = c.ex param n p₁ y₁) ) :=
  Iff.trans c.construction.case (by
    constructor
    · rintro ⟨param, p, y, e, H⟩;
      simp at e; rcases e with ⟨rfl, rfl, rfl⟩
      refine H
    · intro H; exact ⟨_, _, _, rfl, H⟩)

variable (c β)

lemma graph_defined : 𝚺₁-Relation₃ c.Graph via β.graph := by
  intro v; simp [Blueprint.graph, c.construction.fixpoint_defined.iff, Matrix.empty_eq]; rfl

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v β.graph.val ↔ c.Graph (v 0) (v 1) (v 2) := (graph_defined β c).df.iff v

@[definability, simp] instance graph_definable : 𝚺₁-Relation₃ c.Graph := Defined.to_definable _ c.graph_defined

variable {β}

lemma graph_dom_uformula {p r} :
    c.Graph param p r → L.UFormula p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {n k r v y} (hkr : L.Rel k r) (hv : L.SemitermVec k n v) :
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

lemma graph_nrel_iff {n k r v y} (hkr : L.Rel k r) (hv : L.SemitermVec k n v) :
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

lemma graph_rel {n k r v} (hkr : L.Rel k r) (hv : L.SemitermVec k n v) :
    c.Graph param (^rel n k r v) (c.rel param n k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {n k r v} (hkr : L.Rel k r) (hv : L.SemitermVec k n v) :
    c.Graph param (^nrel n k r v) (c.nrel param n k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨n, k, r, v, rfl, rfl⟩⟩

lemma graph_verum (n : V) :
    c.Graph param (^⊤[n]) (c.verum param n) :=
  (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_falsum (n : V) :
    c.Graph param (^⊥[n]) (c.falsum param n) :=
  (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, rfl, rfl⟩⟩

lemma graph_and {n p₁ p₂ r₁ r₂ : V} (hp₁ : L.Semiformula n p₁) (hp₂ : L.Semiformula n p₂)
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

lemma graph_or {n p₁ p₂ r₁ r₂ : V} (hp₁ : L.Semiformula n p₁) (hp₂ : L.Semiformula n p₂)
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

lemma graph_all {n p₁ r₁ : V} (hp₁ : L.Semiformula (n + 1) p₁) (h₁ : c.Graph (c.allChanges param n) p₁ r₁) :
    c.Graph param (^∀[n] p₁) (c.all param n p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n,
    p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_all_inv {n p₁ r : V} :
    c.Graph param (^∀[n] p₁) r → ∃ r₁, c.Graph (c.allChanges param n) p₁ r₁ ∧ r = c.all param n p₁ r₁ := by
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

lemma graph_ex {n p₁ r₁ : V} (hp₁ : L.Semiformula (n + 1) p₁) (h₁ : c.Graph (c.exChanges param n) p₁ r₁) :
    c.Graph param (^∃[n] p₁) (c.ex param n p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨n,
    p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_ex_inv {n p₁ r : V} :
    c.Graph param (^∃[n] p₁) r → ∃ r₁, c.Graph (c.exChanges param n) p₁ r₁ ∧ r = c.ex param n p₁ r₁ := by
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

lemma graph_exists {p : V} : L.UFormula p → ∃ y, c.Graph param p y := by
  haveI : 𝚺₁-Function₂ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₂ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun p param ↦ max param (max (c.allChanges param (fstIdx p)) (c.exChanges param (fstIdx p)))
  have hf : 𝚺₁-Function₂ f := by simp [f]; definability
  apply sigma₁_order_ball_induction hf ?_ ?_ p param
  · definability
  intro p param ih hp
  rcases hp.case with
    (⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, k, r, v, hkr, hv, rfl⟩ |
    ⟨n, rfl⟩ | ⟨n, rfl⟩ |
    ⟨n, p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨n, p₁, p₂, hp₁, hp₂, rfl⟩ |
    ⟨n, p₁, hp₁, rfl⟩ | ⟨n, p₁, hp₁, rfl⟩)
  · exact ⟨c.rel param n k r v, c.graph_rel hkr hv⟩
  · exact ⟨c.nrel param n k r v, c.graph_nrel hkr hv⟩
  · exact ⟨c.verum param n, c.graph_verum n⟩
  · exact ⟨c.falsum param n, c.graph_falsum n⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁.1 with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂.1 with ⟨y₂, h₂⟩
    exact ⟨c.and param n p₁ p₂ y₁ y₂, c.graph_and hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁.1 with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂.1 with ⟨y₂, h₂⟩
    exact ⟨c.or param n p₁ p₂ y₁ y₂, c.graph_or hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) (c.allChanges param n) (by simp [f]) hp₁.1 with ⟨y₁, h₁⟩
    exact ⟨c.all param n p₁ y₁, c.graph_all hp₁ h₁⟩
  · rcases ih p₁ (by simp) (c.exChanges param n) (by simp [f]) hp₁.1 with ⟨y₁, h₁⟩
    exact ⟨c.ex param n p₁ y₁, c.graph_ex hp₁ h₁⟩

lemma graph_unique {p : V} : L.UFormula p → ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r' := by
  apply Language.UFormula.induction 𝚷 (P := fun p ↦ ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r')
    (by definability)
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
    intro n p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_and_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_and_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hor =>
    intro n p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_or_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_or_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hall =>
    intro n p _ ih param r r' hr hr'
    rcases c.graph_all_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_all_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl
  case hex =>
    intro n p _ ih param r r' hr hr'
    rcases c.graph_ex_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_ex_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl

lemma exists_unique {p : V} (hp : L.UFormula p) : ∃! r, c.Graph param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique hp hr' hr)

lemma exists_unique_all (p : V) : ∃! r, (L.UFormula p → c.Graph param p r) ∧ (¬L.UFormula p → r = 0) := by
  by_cases hp : L.UFormula p <;> simp [hp, exists_unique]

def result (p : V) : V := Classical.choose! (c.exists_unique_all param p)

lemma result_prop {p : V} (hp : L.UFormula p) : c.Graph param p (c.result param p) :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬L.UFormula p) : c.result param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph param p r) : c.result param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all param p) (by simp [c.graph_dom_uformula h, h])

@[simp] lemma result_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    c.result param (^rel n k R v) = c.rel param n k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    c.result param (^nrel n k R v) = c.nrel param n k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum {n} : c.result param ^⊤[n] = c.verum param n := c.result_eq_of_graph (c.graph_verum n)

@[simp] lemma result_falsum {n} : c.result param ^⊥[n] = c.falsum param n := c.result_eq_of_graph (c.graph_falsum n)

@[simp] lemma result_and {n p q}
    (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    c.result param (p ^⋏[n] q) = c.and param n p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp.1) (c.result_prop param hq.1))

@[simp] lemma result_or {n p q}
    (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    c.result param (p ^⋎[n] q) = c.or param n p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp.1) (c.result_prop param hq.1))

@[simp] lemma result_all {n p} (hp : L.Semiformula (n + 1) p) :
    c.result param (^∀[n] p) = c.all param n p (c.result (c.allChanges param n) p) :=
  c.result_eq_of_graph (c.graph_all hp (c.result_prop (c.allChanges param n) hp.1))

@[simp] lemma result_ex {n p} (hp : L.Semiformula (n + 1) p) :
    c.result param (^∃[n] p) = c.ex param n p (c.result (c.exChanges param n) p) :=
  c.result_eq_of_graph (c.graph_ex hp (c.result_prop _ hp.1))

section

lemma result_defined : 𝚺₁-Function₂ c.result via β.result := by
  intro v
  simp [Blueprint.result, HSemiformula.val_sigma, eval_uformulaDef L, (uformula_defined L).proper.iff', c.eval_graphDef]
  exact Classical.choose!_eq_iff (c.exists_unique_all (v 1) (v 2))

@[definability] instance result_definable : 𝚺₁-Function₂ c.result := c.result_defined.to_definable _

end

lemma uformula_result_induction {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ param n k R v, L.Rel k R → L.SemitermVec k n v → P param (^rel n k R v) (c.rel param n k R v))
    (hNRel : ∀ param n k R v, L.Rel k R → L.SemitermVec k n v → P param (^nrel n k R v) (c.nrel param n k R v))
    (hverum : ∀ param n, P param (^⊤[n]) (c.verum param n))
    (hfalsum : ∀ param n, P param (^⊥[n]) (c.falsum param n))
    (hand : ∀ param n p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋏[n] q) (c.and param n p q (c.result param p) (c.result param q)))
    (hor : ∀ param n p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋎[n] q) (c.or param n p q (c.result param p) (c.result param q)))
    (hall : ∀ param n p, L.Semiformula (n + 1) p →
      P (c.allChanges param n) p (c.result (c.allChanges param n) p) →
      P param (^∀[n] p) (c.all param n p (c.result (c.allChanges param n) p)))
    (hex : ∀ param n p, L.Semiformula (n + 1) p →
      P (c.exChanges param n) p (c.result (c.exChanges param n) p) →
      P param (^∃[n] p) (c.ex param n p (c.result (c.exChanges param n) p))) :
    ∀ {param p : V}, L.UFormula p → P param p (c.result param p) := by
  haveI : 𝚺₁-Function₂ c.result := c.result_definable
  intro param p
  haveI : 𝚺₁-Function₂ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₂ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun p param ↦ max param (max (c.allChanges param (fstIdx p)) (c.exChanges param (fstIdx p)))
  have hf : 𝚺₁-Function₂ f :=
    DefinableFunction.comp₂_infer (f := Max.max)
      (DefinableFunction.var _)
      (DefinableFunction.comp₂_infer
        (DefinableFunction.comp₂_infer (DefinableFunction.var _) (DefinableFunction.comp₁_infer (DefinableFunction.var _)))
        (DefinableFunction.comp₂_infer (DefinableFunction.var _) (DefinableFunction.comp₁_infer (DefinableFunction.var _))))
  apply sigma₁_order_ball_induction hf ?_ ?_ p param
  · apply Definable.imp
      (Definable.comp₁_infer (DefinableFunction.var _))
      (Definable.comp₃_infer
        (DefinableFunction.var _)
        (DefinableFunction.var _)
        (DefinableFunction.comp₂_infer (DefinableFunction.var _) (DefinableFunction.var _)))
  intro p param ih hp
  rcases hp.case with
    (⟨n, k, r, v, hkr, hv, rfl⟩ | ⟨n, k, r, v, hkr, hv, rfl⟩ |
    ⟨n, rfl⟩ | ⟨n, rfl⟩ |
    ⟨n, p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨n, p₁, p₂, hp₁, hp₂, rfl⟩ |
    ⟨n, p₁, hp₁, rfl⟩ | ⟨n, p₁, hp₁, rfl⟩)
  · simpa [hkr, hv] using hRel param n k r v hkr hv
  · simpa [hkr, hv] using hNRel param n k r v hkr hv
  · simpa using hverum param n
  · simpa using hfalsum param n
  · simpa [c.result_and hp₁ hp₂] using
      hand param n p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁.1) (ih p₂ (by simp) param (by simp [f]) hp₂.1)
  · simpa [c.result_or hp₁ hp₂] using
      hor param n p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁.1) (ih p₂ (by simp) param (by simp [f]) hp₂.1)
  · simpa [c.result_all hp₁] using
      hall param n p₁ hp₁ (ih p₁ (by simp) (c.allChanges param n) (by simp [f]) hp₁.1)
  · simpa [c.result_ex hp₁] using
      hex param n p₁ hp₁ (ih p₁ (by simp) (c.exChanges param n) (by simp [f]) hp₁.1)

lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ param n k R v, L.Rel k R → L.SemitermVec k n v → P param n (^rel n k R v) (c.rel param n k R v))
    (hNRel : ∀ param n k R v, L.Rel k R → L.SemitermVec k n v → P param n (^nrel n k R v) (c.nrel param n k R v))
    (hverum : ∀ param n, P param n (^⊤[n]) (c.verum param n))
    (hfalsum : ∀ param n, P param n (^⊥[n]) (c.falsum param n))
    (hand : ∀ param n p q, L.Semiformula n p → L.Semiformula n q →
      P param n p (c.result param p) → P param n q (c.result param q) → P param n (p ^⋏[n] q) (c.and param n p q (c.result param p) (c.result param q)))
    (hor : ∀ param n p q, L.Semiformula n p → L.Semiformula n q →
      P param n p (c.result param p) → P param n q (c.result param q) → P param n (p ^⋎[n] q) (c.or param n p q (c.result param p) (c.result param q)))
    (hall : ∀ param n p, L.Semiformula (n + 1) p →
      P (c.allChanges param n) (n + 1) p (c.result (c.allChanges param n) p) →
      P param n (^∀[n] p) (c.all param n p (c.result (c.allChanges param n) p)))
    (hex : ∀ param n p, L.Semiformula (n + 1) p →
      P (c.exChanges param n) (n + 1) p (c.result (c.exChanges param n) p) →
      P param n (^∃[n] p) (c.ex param n p (c.result (c.exChanges param n) p))) :
    ∀ {param n p : V}, L.Semiformula n p → P param n p (c.result param p) := by
  suffices ∀ {param p : V}, L.UFormula p → ∀ n ≤ p, n = fstIdx p → P param n p (c.result param p)
  by intro param n p hp; exact @this param p hp.1 n (by simp [hp.2]) hp.2
  intro param p hp
  apply c.uformula_result_induction (P := fun param p y ↦ ∀ n ≤ p, n = fstIdx p → P param n p y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · apply Definable.ball_le (DefinableFunction.var _)
    simp_all only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two,
      Fin.succ_zero_eq_one]
    apply LO.FirstOrder.Arith.Definable.imp
    · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
      apply LO.FirstOrder.Arith.Definable.comp₂_infer
      · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.DefinableFunction.comp₁_infer
        simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
    · apply LO.FirstOrder.Arith.Definable.comp₄_infer
      · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.DefinableFunction.comp₁_infer
        simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
      · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
      · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
  · rintro param n k R v hkR hv _ _ rfl; simpa using hRel param n k R v hkR hv
  · rintro param n k R v hkR hv _ _ rfl; simpa using hNRel param n k R v hkR hv
  · rintro param n _ _ rfl; simpa using hverum param n
  · rintro param n _ _ rfl; simpa using hfalsum param n
  · rintro param n p q hp hq ihp ihq _ _ rfl
    have ihp : P param n p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param n q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hand param n p q hp hq ihp ihq
  · rintro param n p q hp hq ihp ihq _ _ rfl
    have ihp : P param n p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param n q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hor param n p q hp hq ihp ihq
  · rintro param n p hp ihp _ _ rfl
    have ihp : P (c.allChanges param n) (n + 1) p (c.result (c.allChanges param n) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hall param n p hp ihp
  · rintro param n p hp ihp _ _ rfl
    have ihp : P (c.exChanges param n) (n + 1) p (c.result (c.exChanges param n) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hex param n p hp ihp

end Construction

end Language.UformulaRec1

/-
namespace Language.UformulaRec

structure Blueprint (pL : LDef) (arity : ℕ) where
  rel        : 𝚺₁-Semisentence (arity + 5)
  nrel       : 𝚺₁-Semisentence (arity + 5)
  verum      : 𝚺₁-Semisentence (arity + 2)
  falsum     : 𝚺₁-Semisentence (arity + 2)
  and        : 𝚺₁-Semisentence (arity + 6)
  or         : 𝚺₁-Semisentence (arity + 6)
  all        : 𝚺₁-Semisentence (arity + 4)
  ex         : 𝚺₁-Semisentence (arity + 4)
  allChanges : Fin arity → 𝚺₁-Semisentence (arity + 2)
  exChanges  : Fin arity → 𝚺₁-Semisentence (arity + 2)

structure Construction (L : Arith.Language V) {arity} (φ : Blueprint pL arity) where
  rel                        (param : Fin arity → V) (n k R v : V) : V
  nrel                       (param : Fin arity → V) (n k R v : V) : V
  verum                      (param : Fin arity → V) (n : V) : V
  falsum                     (param : Fin arity → V) (n : V) : V
  and                        (param : Fin arity → V) (n p₁ p₂ y₁ y₂ : V) : V
  or                         (param : Fin arity → V) (n p₁ p₂ y₁ y₂ : V) : V
  all                        (param : Fin arity → V) (n p₁ y₁ : V) : V
  ex                         (param : Fin arity → V) (n p₁ y₁ : V) : V
  allChanges (i : Fin arity) (param : Fin arity → V) (n : V) : V
  exChanges  (i : Fin arity) (param : Fin arity → V) (n : V) : V
  rel_defined    : DefinedFunction (fun v ↦ rel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.rel
  nrel_defined   : DefinedFunction (fun v ↦ nrel (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.nrel
  verum_defined  : DefinedFunction (fun v ↦ verum (v ·.succ) (v 0)) φ.verum
  falsum_defined : DefinedFunction (fun v ↦ falsum (v ·.succ) (v 0)) φ.falsum
  and_defined    : DefinedFunction (fun v ↦ and (v ·.succ.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3) (v 4)) φ.and
  or_defined     : DefinedFunction (fun v ↦ or  (v ·.succ.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3) (v 4)) φ.or
  all_defined    : DefinedFunction (fun v ↦ all (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.all
  ex_defined     : DefinedFunction (fun v ↦ ex  (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) φ.ex
  allChanges_defined (i : Fin arity) : DefinedFunction (fun v ↦ allChanges i (v ·.succ) (v 0)) (φ.allChanges i)
  exChanges_defined  (i : Fin arity) : DefinedFunction (fun v ↦ exChanges i (v ·.succ) (v 0)) (φ.exChanges i)

variable {arity} (β : Blueprint pL arity)

namespace Blueprint

def decomp {n : ℕ} (s : 𝚺₁-Semisentence n) : 𝚺₁-Semisentence 1 :=
  .mkSigma (∃^[n] (Matrix.conj fun i : Fin n ↦
    (unNpairDef i).val/[#(i.natAdd 1), #⟨n, by simp⟩]) ⋏ (Rew.substs fun i : Fin n ↦ #(i.natAdd 1)).hom s) (by simp)

def toRec1 : UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param n k R v | !qqNRelDef y n k R v” (by simp)
  nrel := .mkSigma “y param n k R v | !qqRelDef y n k R v” (by simp)
  verum := .mkSigma “y param n | !qqFalsumDef y n” (by simp)
  falsum := .mkSigma “y param n | !qqVerumDef y n” (by simp)
  and := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqOrDef y n y₁ y₂” (by simp)
  or := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqAndDef y n y₁ y₂” (by simp)
  all := .mkSigma “y param n p₁ y₁ | !qqExDef y n y₁” (by simp)
  ex := .mkSigma “y param n p₁ y₁ | !qqAllDef y n y₁” (by simp)
  allChanges := .mkSigma “param' param n | param' = 0” (by simp)
  exChanges := .mkSigma “param' param n | param' = 0” (by simp)

end Blueprint

end Language.UformulaRec
-/

end LO.Arith

end
