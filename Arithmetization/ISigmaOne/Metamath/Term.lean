import Arithmetization.ISigmaOne.Metamath.Language
import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace FormalizedTerm

variable {L : Model.Language M} {pL : LDef} [Model.Language.Defined L pL]

abbrev qqBvar (z : M) : M := ⟪0, z⟫ + 1

abbrev qqFvar (x : M) : M := ⟪1, x⟫ + 1

abbrev qqFunc (k f v : M) : M := ⟪2, ⟪k, ⟪f, v⟫⟫⟫ + 1

scoped prefix:max "^#" => qqBvar

scoped prefix:max "^&" => qqFvar

scoped prefix:max "^func " => qqFunc

@[simp] lemma arity_lt_qqFunc (k f v : M) : k < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right 2 k) <| pair_le_pair_right 2 <| le_pair_left k ⟪f, v⟫

@[simp] lemma func_lt_qqFunc (k f v : M) : f < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

@[simp] lemma terms_lt_qqFunc (k f v : M) : v < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

variable (L)

def Phi (n : M) (C : Set M) (t : M) : Prop :=
  (∃ z < n, t = ^#z) ∨ (∃ x, t = ^&x) ∨ (∃ k f v : M, L.Func k f ∧ Seq v ∧ k = lh v ∧ (∀ i u, ⟪i, u⟫ ∈ v → u ∈ C) ∧ t = ^func k f v)

private lemma phi_iff (n : M) (C : M) (t : M) :
    Phi L n {x | x ∈ C} t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x < t, t = ^&x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t, L.Func k f ∧ Seq v ∧ k = lh v ∧ (∀ i < v, ∀ u < v, ⟪i, u⟫ ∈ v → u ∈ C) ∧ t = ^func k f v) where
  mp := by
    rintro (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, Sv, hk, hv, rfl⟩)
    · left; exact ⟨z, hz, rfl⟩
    · right; left
      exact ⟨x, lt_succ_iff_le.mpr <| by simp, rfl⟩
    · right; right
      exact ⟨k, by simp, f, by simp, v, by simp, hkf, Sv, hk, fun i _ u _ hi ↦ hv i u hi, rfl⟩
  mpr := by
    unfold Phi
    rintro (⟨z, hz, rfl⟩ | ⟨x, _, rfl⟩ | ⟨k, _, f, _, v, _, hkf, Sv, hk, hv, rfl⟩)
    · left; exact ⟨z, hz, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right; exact ⟨k, f, v, hkf, Sv, hk,
        fun i u hi ↦ hv i (lt_of_mem_dom hi) u (lt_of_mem_rng hi) hi, rfl⟩

def _root_.LO.FirstOrder.Arith.qqBvarDef : 𝚺₀-Semisentence 2 := .mkSigma “t z | ∃ t' < t, !pairDef t' 0 z ∧ t = t' + 1” (by simp)

lemma qqBvar_defined : 𝚺₀-Function₁ (qqBvar : M → M) via qqBvarDef := by
  intro v; simp [qqBvarDef]
  constructor
  · intro h; exact ⟨⟪0, v 1⟫, by simp [h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqBvarDef (v) :
    Semiformula.Evalbm M v qqBvarDef.val ↔ v 0 = ^#(v 1) := qqBvar_defined.df.iff v

def _root_.LO.FirstOrder.Arith.qqFvarDef : 𝚺₀-Semisentence 2 := .mkSigma “t x | ∃ t' < t, !pairDef t' 1 x ∧ t = t' + 1” (by simp)

lemma qqFvar_defined : 𝚺₀-Function₁ (qqFvar : M → M) via qqFvarDef := by
  intro v; simp [qqFvarDef]
  constructor
  · intro h; exact ⟨⟪1, v 1⟫, by simp [h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqFvarDef (v) :
    Semiformula.Evalbm M v qqFvarDef.val ↔ v 0 = ^&(v 1) := qqFvar_defined.df.iff v

private lemma qqFunc_graph {x k f v : M} :
    x = ^func k f v ↔ ∃ fv < x, fv = ⟪f, v⟫ ∧ ∃ kfv < x, kfv = ⟪k, fv⟫ ∧ ∃ x' < x, x' = ⟪2, kfv⟫ ∧ x = x' + 1 :=
  ⟨by rintro rfl
      exact ⟨⟪f, v⟫, lt_succ_iff_le.mpr <| le_trans (le_pair_right _ _) (le_pair_right _ _), rfl,
        ⟪k, ⟪f, v⟫⟫, lt_succ_iff_le.mpr <| by simp, rfl,
        ⟪2, ⟪k, ⟪f, v⟫⟫⟫, by simp, rfl, rfl⟩,
   by rintro ⟨_, _, rfl, _, _, rfl, _, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arith.qqFuncDef : 𝚺₀-Semisentence 4 := .mkSigma
  “x k f v | ∃ fv < x, !pairDef fv f v ∧ ∃ kfv < x, !pairDef kfv k fv ∧ ∃ x' < x, !pairDef x' 2 kfv ∧ x = x' + 1” (by simp)

lemma qqFunc_defined : 𝚺₀-Function₃ (qqFunc : M → M → M → M) via qqFuncDef := by
  intro v; simp [qqFuncDef, qqFunc_graph]

@[simp] lemma eval_qqFuncDef (v) :
    Semiformula.Evalbm M v qqFuncDef.val ↔ v 0 = ^func (v 1) (v 2) (v 3) := qqFunc_defined.df.iff v

variable (pL)

def formula : Fixpoint.Formula 1 := ⟨.ofZero (.mkSigma
  “t C n |
    (∃ z < n, !qqBvarDef t z) ∨
    (∃ x < t, !qqFvarDef t x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t, !pL.func k f ∧ :Seq v ∧ !lhDef k v ∧ (∀ i < v, ∀ u < v, i ~[v] u → u ∈ C) ∧ !qqFuncDef t k f v)”
  (by simp)) _⟩

variable {pL}

def construction : Fixpoint.Construction M (formula pL) where
  Φ := fun n ↦ Phi L (n 0)
  defined := .of_zero <| by intro v; simp [phi_iff, Language.Defined.eval_func (L := L) (pL := pL)]
  monotone := by
    rintro C C' hC v x (h | h | ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)
    · exact Or.inl h
    · exact Or.inr <| Or.inl h
    · exact Or.inr <| Or.inr ⟨k, f, v, hkf, Sv, hk, fun i u hi ↦ hC (h i u hi), rfl⟩
  finite := by
    rintro C v x (h | h | ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)
    · exact Or.inl h
    · exact Or.inr <| Or.inl h
    · exact Or.inr <| Or.inr ⟨k, f, v, hkf, Sv, hk, fun i u hi ↦
        ⟨h i u hi, _root_.lt_trans (lt_of_mem_rng hi) (by simp)⟩, rfl⟩

end FormalizedTerm

open FormalizedTerm

variable (L : Model.Language M) {pL : LDef} [Model.Language.Defined L pL]

def IsSemiterm (n : M) : M → Prop := (construction L).Fixpoint ![n]

variable (pL)

def _root_.LO.FirstOrder.Arith.isSemitermDef : 𝚫₁-Semisentence 2 := (formula pL).fixpointDef.rew (Rew.substs ![#1, #0])

variable {pL}

lemma isSemiterm_defined : 𝚫₁-Relation (IsSemiterm L) via (isSemitermDef pL) :=
  ⟨HSemiformula.ProperOn.rew (construction L).fixpoint_defined.proper _,
   by intro v; simp [isSemitermDef, (construction L).eval_fixpointDef]; rfl⟩

variable {L}

variable {n : M}

local prefix:80 "𝐓ⁿ " => IsSemiterm L n

lemma IsSemiterm.case {t : M} :
    𝐓ⁿ t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : M, L.Func k f ∧ Seq v ∧ k = lh v ∧ (∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u) ∧ t = ^func k f v) :=
  (construction L).case

lemma IsSemiterm.bvar {z : M} (hz : z < n) : 𝐓ⁿ ^#z := IsSemiterm.case.mpr (Or.inl ⟨z, hz, rfl⟩)

lemma IsSemiterm.fvar (x : M) : 𝐓ⁿ ^&x := IsSemiterm.case.mpr (Or.inr <| Or.inl ⟨x, rfl⟩)

lemma IsSemiterm.func {k f v : M} (hkf : L.Func k f) (Sv : Seq v) (hk : k = lh v)
    (h : ∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u) :
    𝐓ⁿ ^func k f v := IsSemiterm.case.mpr (Or.inr <| Or.inr ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)

lemma IsSemiterm.induction {Γ} {P : M → Prop} (hP : (Γ, 1)-Predicate P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.Func k f → Seq v → k = lh v → (∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u ∧ P u) → P (^func k f v)) :
    ∀ t, 𝐓ⁿ t → P t :=
  (construction L).induction (v := ![n]) hP (by
    rintro C hC x (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)
    · exact hbvar z hz
    · exact hfvar x
    · exact hfunc k f v hkf Sv hk (fun i u hi ↦ hC u (h i u hi)))

end LO.FirstOrder.Arith.Model

end
