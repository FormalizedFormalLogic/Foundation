import Arithmetization.ISigmaOne.Metamath.Language
import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

variable {L : Model.Language M} {pL : LDef} [Model.Language.Defined L pL]

section term

def qqBvar (z : M) : M := ⟪0, z⟫ + 1

def qqFvar (x : M) : M := ⟪1, x⟫ + 1

def qqFunc (k f v : M) : M := ⟪2, ⟪k, ⟪f, v⟫⟫⟫ + 1

scoped prefix:max "^#" => qqBvar

scoped prefix:max "^&" => qqFvar

scoped prefix:max "^func " => qqFunc

@[simp] lemma var_lt_qqBvar (z : M) : z < ^#z := lt_succ_iff_le.mpr <| le_pair_right 0 z

@[simp] lemma var_lt_qqFvar (x : M) : x < ^&x := lt_succ_iff_le.mpr <| le_pair_right 1 x

@[simp] lemma arity_lt_qqFunc (k f v : M) : k < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right 2 k) <| pair_le_pair_right 2 <| le_pair_left k ⟪f, v⟫

@[simp] lemma func_lt_qqFunc (k f v : M) : f < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

@[simp] lemma terms_lt_qqFunc (k f v : M) : v < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

lemma lt_qqFunc_of_mem {i b k f v : M} (hi : ⟪i, b⟫ ∈ v) : b < ^func k f v :=
  _root_.lt_trans (lt_of_mem_rng hi) (terms_lt_qqFunc k f v)

@[simp] lemma qqBvar_inj {z z' : M} : ^#z = ^#z' ↔ z = z' := by simp [qqBvar]

@[simp] lemma qqFvar_inj {x x' : M} : ^&x = ^&x' ↔ x = x' := by simp [qqFvar]

@[simp] lemma qqFunc_inj {k f v k' f' v' : M} : ^func k f v = ^func k' f' v' ↔ k = k' ∧ f = f' ∧ v = v' := by simp [qqFunc]

def _root_.LO.FirstOrder.Arith.qqBvarDef : 𝚺₀-Semisentence 2 := .mkSigma “t z | ∃ t' < t, !pairDef t' 0 z ∧ t = t' + 1” (by simp)

lemma qqBvar_defined : 𝚺₀-Function₁ (qqBvar : M → M) via qqBvarDef := by
  intro v; simp [qqBvarDef]
  constructor
  · intro h; exact ⟨⟪0, v 1⟫, by simp [qqBvar, h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqBvarDef (v) :
    Semiformula.Evalbm M v qqBvarDef.val ↔ v 0 = ^#(v 1) := qqBvar_defined.df.iff v

def _root_.LO.FirstOrder.Arith.qqFvarDef : 𝚺₀-Semisentence 2 := .mkSigma “t x | ∃ t' < t, !pairDef t' 1 x ∧ t = t' + 1” (by simp)

lemma qqFvar_defined : 𝚺₀-Function₁ (qqFvar : M → M) via qqFvarDef := by
  intro v; simp [qqFvarDef]
  constructor
  · intro h; exact ⟨⟪1, v 1⟫, by simp [qqFvar, h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqFvarDef (v) :
    Semiformula.Evalbm M v qqFvarDef.val ↔ v 0 = ^&(v 1) := qqFvar_defined.df.iff v

private lemma qqFunc_graph {x k f v : M} :
    x = ^func k f v ↔ ∃ fv < x, fv = ⟪f, v⟫ ∧ ∃ kfv < x, kfv = ⟪k, fv⟫ ∧ ∃ x' < x, x' = ⟪2, kfv⟫ ∧ x = x' + 1 :=
  ⟨by rintro rfl
      exact ⟨⟪f, v⟫, lt_succ_iff_le.mpr <| le_trans (le_pair_right _ _) (le_pair_right _ _), rfl,
        ⟪k, ⟪f, v⟫⟫, lt_succ_iff_le.mpr <| by simp, rfl,
        ⟪2, ⟪k, ⟪f, v⟫⟫⟫, by simp [qqFunc], rfl, rfl⟩,
   by rintro ⟨_, _, rfl, _, _, rfl, _, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arith.qqFuncDef : 𝚺₀-Semisentence 4 := .mkSigma
  “x k f v | ∃ fv < x, !pairDef fv f v ∧ ∃ kfv < x, !pairDef kfv k fv ∧ ∃ x' < x, !pairDef x' 2 kfv ∧ x = x' + 1” (by simp)

lemma qqFunc_defined : 𝚺₀-Function₃ (qqFunc : M → M → M → M) via qqFuncDef := by
  intro v; simp [qqFuncDef, qqFunc_graph]

@[simp] lemma eval_qqFuncDef (v) :
    Semiformula.Evalbm M v qqFuncDef.val ↔ v 0 = ^func (v 1) (v 2) (v 3) := qqFunc_defined.df.iff v

namespace FormalizedTerm

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

def formula (pL : LDef) : Fixpoint.Formula 1 := ⟨.ofZero (.mkSigma
  “t C n |
    (∃ z < n, !qqBvarDef t z) ∨
    (∃ x < t, !qqFvarDef t x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t, !pL.func k f ∧ :Seq v ∧ !lhDef k v ∧ (∀ i < v, ∀ u < v, i ~[v] u → u ∈ C) ∧ !qqFuncDef t k f v)”
  (by simp)) _⟩

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

variable (L)

def Language.IsSemiterm (n : M) : M → Prop := (construction L).Fixpoint ![n]

def _root_.LO.FirstOrder.Arith.LDef.isSemitermDef (pL : LDef) : 𝚫₁-Semisentence 2 := (formula pL).fixpointDef.rew (Rew.substs ![#1, #0])

lemma isSemiterm_defined : 𝚫₁-Relation L.IsSemiterm via pL.isSemitermDef :=
  ⟨HSemiformula.ProperOn.rew (construction L).fixpoint_defined.proper _,
   by intro v; simp [LDef.isSemitermDef, (construction L).eval_fixpointDef]; rfl⟩

@[simp] lemma eval_isSemitermDef (v) :
    Semiformula.Evalbm M v pL.isSemitermDef.val ↔ L.IsSemiterm (v 0) (v 1) := (isSemiterm_defined L).df.iff v

instance isSemitermDef_definable : 𝚫₁-Relation (L.IsSemiterm) := Defined.to_definable _ (isSemiterm_defined L)

@[simp, definability] instance isSemitermDef_definable' (Γ) : (Γ, m + 1)-Relation (L.IsSemiterm) :=
  .of_deltaOne (isSemitermDef_definable L) _ _

variable {L}

variable {n : M}

local prefix:80 "𝐓ⁿ " => L.IsSemiterm n

lemma Language.IsSemiterm.case_iff {t : M} :
    𝐓ⁿ t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : M, L.Func k f ∧ Seq v ∧ k = lh v ∧ (∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u) ∧ t = ^func k f v) :=
  (construction L).case

alias ⟨Language.IsSemiterm.case, Language.IsSemiterm.mk⟩ := Language.IsSemiterm.case_iff

@[simp] lemma IsSemiterm.bvar {z : M} : 𝐓ⁿ ^#z ↔ z < n :=
  ⟨by intro h
      rcases h.case with (⟨z', hz, hzz'⟩ | ⟨x, h⟩ | ⟨k, f, v, _, _, _, _, h⟩)
      · rcases (show z = z' from by simpa using hzz'); exact hz
      · simp [qqBvar, qqFvar] at h
      · simp [qqBvar, qqFunc] at h,
    fun hz ↦ Language.IsSemiterm.mk (Or.inl ⟨z, hz, rfl⟩)⟩

@[simp] lemma IsSemiterm.fvar (x : M) : 𝐓ⁿ ^&x := Language.IsSemiterm.mk (Or.inr <| Or.inl ⟨x, rfl⟩)

lemma IsSemiterm.func {k f v : M} (hkf : L.Func k f) (Sv : Seq v) (hk : k = lh v)
    (h : ∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u) :
    𝐓ⁿ (^func k f v) := Language.IsSemiterm.mk (Or.inr <| Or.inr ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)

lemma IsSemiterm.func_iff {k f v : M} :
    𝐓ⁿ (^func k f v) ↔ L.Func k f ∧ Seq v ∧ k = lh v ∧ ∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u :=
  ⟨by intro h
      rcases h.case with (⟨_, _, h⟩ | ⟨x, h⟩ | ⟨k', f', v', hkf, Sv, hk, hv, h⟩)
      · simp [qqFunc, qqBvar] at h
      · simp [qqFunc, qqFvar] at h
      · rcases (show k = k' ∧ f = f' ∧ v = v' by simpa [qqFunc] using h) with ⟨rfl, rfl, rfl⟩
        exact ⟨hkf, Sv, hk, hv⟩,
   by rintro ⟨hkf, Sv, hk, hv⟩; exact IsSemiterm.func hkf Sv hk hv⟩

lemma IsSemiterm.induction (Γ) {P : M → Prop} (hP : (Γ, 1)-Predicate P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.Func k f → Seq v → k = lh v → (∀ i u, ⟪i, u⟫ ∈ v → 𝐓ⁿ u ∧ P u) → P (^func k f v)) :
    ∀ t, 𝐓ⁿ t → P t :=
  (construction L).induction (v := ![n]) hP (by
    rintro C hC x (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, Sv, hk, h, rfl⟩)
    · exact hbvar z hz
    · exact hfvar x
    · exact hfunc k f v hkf Sv hk (fun i u hi ↦ hC u (h i u hi)))

end term

section termSubst

variable (L)

def TermSeq (n m w : M) : Prop := Seq w ∧ n = lh w ∧ ∀ i u, ⟪i, u⟫ ∈ w → L.IsSemiterm m u

variable {L}

protected lemma TermSeq.seq {n m w : M} (h : TermSeq L n m w) : Seq w := h.1

protected lemma TermSeq.lh {n m w : M} (h : TermSeq L n m w) : n = lh w := h.2.1

lemma TermSeq.prop {n m w : M} (h : TermSeq L n m w) : ∀ i u, ⟪i, u⟫ ∈ w → L.IsSemiterm m u := h.2.2

section

private lemma termSeq_iff (n m w : M) :
    TermSeq L n m w ↔ Seq w ∧ n = lh w ∧ ∀ i < w, ∀ u < w, ⟪i, u⟫ ∈ w → L.IsSemiterm m u :=
  ⟨fun h ↦ ⟨TermSeq.seq h, TermSeq.lh h, fun i _ u _ hi ↦ TermSeq.prop h i u hi⟩,
   by rintro ⟨Sw, hn, h⟩
      exact ⟨by simpa using Sw, by simpa using hn,
        fun i u hi ↦ by simpa using h i (lt_of_mem_dom <| by simpa using hi) u (lt_of_mem_rng <| by simpa using hi) (by simpa using hi)⟩⟩

def _root_.LO.FirstOrder.Arith.LDef.termSeqDef (pL : LDef) : 𝚫₁-Semisentence 3 := .mkDelta
  (.mkSigma
    “n m w | :Seq w ∧ !lhDef n w ∧ ∀ i < w, ∀ u < w, i ~[w] u → !pL.isSemitermDef.sigma m u”
    (by simp))
  (.mkPi
    “n m w | :Seq w ∧ !lhDef n w ∧ ∀ i < w, ∀ u < w, i ~[w] u → !pL.isSemitermDef.pi m u”
    (by simp))

variable (L)

lemma termSeq_defined : 𝚫₁-Relation₃ (TermSeq L) via pL.termSeqDef :=
  ⟨by intro v; simp [LDef.termSeqDef, HSemiformula.val_sigma, eval_isSemitermDef L, (isSemiterm_defined L).proper.iff'],
   by intro v; simp [LDef.termSeqDef, HSemiformula.val_sigma, eval_isSemitermDef L, termSeq_iff]⟩

@[simp] lemma eval_termSeq (v) :
    Semiformula.Evalbm M v pL.termSeqDef.val ↔ TermSeq L (v 0) (v 1) (v 2) := (termSeq_defined L).df.iff v

instance termSeq_definable : 𝚫₁-Relation₃ (TermSeq L) := Defined.to_definable _ (termSeq_defined L)

@[simp, definability] instance termSeq_definable' (Γ) : (Γ, m + 1)-Relation₃ (TermSeq L) :=
  .of_deltaOne (termSeq_definable L) _ _

end

namespace FormalizedTermSubst

variable (L)

def Phi (n m w : M) (C : Set M) (p : M) : Prop :=
  L.IsSemiterm n (π₁ p) ∧ L.IsSemiterm m (π₂ p) ∧
  ( (∃ z < n, π₁ p = ^#z ∧ ⟪z, π₂ p⟫ ∈ w) ∨
    (∃ x, π₁ p = ^&x ∧ π₂ p = ^&x) ∨
    (∃ k f v v', π₁ p = ^func k f v ∧ π₂ p = ^func k f v' ∧ ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → ⟪u, u'⟫ ∈ C) )

private lemma phi_iff (n m w C p : M) :
    Phi L n m w {x | x ∈ C} p ↔
    ∃ t₁ ≤ p, ∃ t₂ ≤ p, p = ⟪t₁, t₂⟫ ∧ L.IsSemiterm n t₁ ∧ L.IsSemiterm m t₂ ∧
    ( (∃ z < n, t₁ = ^#z ∧ ⟪z, t₂⟫ ∈ w) ∨
      (∃ x < t₁, t₁ = ^&x ∧ t₂ = ^&x) ∨
      (∃ k < t₁, ∃ f < t₁, ∃ v < t₁, ∃ v' < t₂, t₁ = ^func k f v ∧ t₂ = ^func k f v' ∧
        (∀ i < v, ∀ u < v, ∀ u' < v', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → ⟪u, u'⟫ ∈ C)) ) := by
  constructor
  ·{intro ⟨hp₁, hp₂, h⟩
    refine ⟨π₁ p, by simp, π₂ p, by simp, by simp, hp₁, hp₂, ?_⟩
    rcases h with (⟨z, hz, h₁, h⟩ | ⟨x, h₁, h₂⟩ | ⟨k, f, v, v', h₁, h₂, h⟩)
    · left; exact ⟨z, hz, h₁, h⟩
    · right; left; exact ⟨x, by simp [h₁], h₁, h₂⟩
    · right; right
      exact ⟨k, by simp [h₁], f, by simp [h₁], v, by simp [h₁], v', by simp [h₂],
        h₁, h₂, fun i _ u _ u' _ hi hi' ↦ h i u u' hi hi'⟩}
  · rintro ⟨t₁, _, t₂, _, rfl, ht₁, ht₂, h⟩
    refine ⟨by simpa using ht₁, by simpa using ht₂, ?_⟩
    rcases h with (⟨z, hz, rfl, h⟩ | ⟨x, _, rfl, rfl⟩ | ⟨k, _, f, _, v, _, v', _, rfl, rfl, h⟩)
    · left; exact ⟨z, hz, by simp [h]⟩
    · right; left; exact ⟨x, by simp⟩
    · right; right
      exact ⟨k, f, v, v', by simp, by simp, fun i u u' hi hi' ↦
        h i (lt_of_mem_dom hi) u (lt_of_mem_rng hi) u' (lt_of_mem_rng hi') hi hi'⟩

def formulaAux : Semisentence ℒₒᵣ 7 := “t₁ t₂ p C n m w |
  (∃ z < n, !qqBvarDef t₁ z ∧ z ~[w] t₂) ∨
  (∃ x < t₁, !qqFvarDef t₁ x ∧ !qqFvarDef t₂ x) ∨
  (∃ k < t₁, ∃ f < t₁, ∃ v < t₁, ∃ v' < t₂, !qqFuncDef t₁ k f v ∧ !qqFuncDef t₂ k f v' ∧
  (∀ i < v, ∀ u < v, ∀ u' < v', i ~[v] u → i ~[v'] u' → u ~[C] u'))”

def formula (pL : LDef) : Fixpoint.Formula 3 := ⟨.mkDelta
  (.mkSigma
    “p C n m w |
      ∃ t₁ <⁺ p, ∃ t₂ <⁺ p, !pairDef p t₁ t₂ ∧ !pL.isSemitermDef.sigma n t₁ ∧ !pL.isSemitermDef.sigma m t₂ ∧
      !formulaAux t₁ t₂ p C n m w”
    (by simp [formulaAux]))
  (.mkPi
    “p C n m w |
      ∃ t₁ <⁺ p, ∃ t₂ <⁺ p, !pairDef p t₁ t₂ ∧ !pL.isSemitermDef.pi n t₁ ∧ !pL.isSemitermDef.pi m t₂ ∧
      !formulaAux t₁ t₂ p C n m w”
    (by simp [formulaAux]))⟩

def construction : Fixpoint.Construction M (formula pL) where
  Φ := fun v ↦ Phi L (v 0) (v 1) (v 2)
  defined := ⟨fun v ↦
    by simp [formula, HSemiformula.val_sigma, eval_isSemitermDef L, (isSemiterm_defined L).proper.iff'],
  fun v ↦ by simpa [formula, HSemiformula.val_sigma, eval_isSemitermDef L, formulaAux] using phi_iff _ _ _ _ _ _⟩
  monotone := by
    rintro C C' hC v p ⟨ht₁, ht₂, (h | h | ⟨k, f, v, v', h₁, h₂, h⟩)⟩
    · exact ⟨ht₁, ht₂, Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inr ⟨k, f, v, v', h₁, h₂, fun i u u' hi hi' ↦ hC (h i u u' hi hi')⟩⟩
  finite := by
    rintro C v p ⟨ht₁, ht₂, (h | h | ⟨k, f, v, v', h₁, h₂, h⟩)⟩
    · exact ⟨ht₁, ht₂, Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inr ⟨k, f, v, v', h₁, h₂, fun i u u' hi hi' ↦ ⟨h i u u' hi hi', by
      have : ⟪u, u'⟫ < ⟪π₁ p, π₂ p⟫ := pair_lt_pair (by simpa [h₁] using lt_qqFunc_of_mem hi) (by simpa [h₂] using lt_qqFunc_of_mem hi')
      simpa using this⟩⟩⟩

def Subst (n m w : M) : M → Prop := (construction L).Fixpoint ![n, m, w]

def _root_.LO.FirstOrder.Arith.LDef.substDef (pL : LDef) : 𝚫₁-Semisentence 4 := (formula pL).fixpointDef.rew <| Rew.substs ![#3, #0, #1, #2]

lemma subst_defined : 𝚫₁-Relation₄ (Subst L) via pL.substDef :=
  ⟨HSemiformula.ProperOn.rew (construction L).fixpoint_defined.proper _,
   by intro v; simp [LDef.substDef, (construction L).eval_fixpointDef, Subst]⟩

@[simp] lemma eval_substDef (v) :
    Semiformula.Evalbm M v pL.substDef.val ↔ Subst L (v 0) (v 1) (v 2) (v 3) := (subst_defined L).df.iff v

instance subst_definable : 𝚫₁-Relation₄ (Subst L) := Defined.to_definable _ (subst_defined L)

@[simp, definability] instance subst_definable' (Γ) : (Γ, m + 1)-Relation₄ (Subst L) :=
  .of_deltaOne (subst_definable L) _ _

variable {L}

lemma Subst.case_iff {n m w p : M} :
    Subst L n m w p ↔
    L.IsSemiterm n (π₁ p) ∧ L.IsSemiterm m (π₂ p) ∧
    ( (∃ z < n, π₁ p = ^#z ∧ ⟪z, π₂ p⟫ ∈ w) ∨
      (∃ x, π₁ p = ^&x ∧ π₂ p = ^&x) ∨
      (∃ k f v v', π₁ p = ^func k f v ∧ π₂ p = ^func k f v' ∧ ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Subst L n m w ⟪u, u'⟫) ) :=
  (construction L).case

alias ⟨Subst.case, Subst.mk⟩ := Subst.case_iff

lemma Subst.semiterm₁ {n m w t t'} (h : Subst L n m w ⟪t, t'⟫) : L.IsSemiterm n t := by simpa using h.case.1

lemma Subst.semiterm₂ {n m w t t'} (h : Subst L n m w ⟪t, t'⟫) : L.IsSemiterm m t' := by simpa using h.case.2.1

lemma Subst.bvar {n m w z u : M} (hz : z < n) (hu : L.IsSemiterm m u) (h : ⟪z, u⟫ ∈ w) :
    Subst L n m w ⟪^#z, u⟫ := Subst.mk ⟨by simp [hz], by simpa using hu, Or.inl ⟨z, hz, by simpa using h⟩⟩

lemma Subst.bvar_iff {n m w z u : M} :
    Subst L n m w ⟪^#z, u⟫ ↔ z < n ∧ L.IsSemiterm m u ∧ ⟪z, u⟫ ∈ w :=
  ⟨by intro h
      rcases h.case with ⟨_, hu, (⟨z', hz', hzz', h⟩ | ⟨x, h, _⟩ | ⟨k, f, v, v', h, _⟩)⟩
      · rcases (show z = z' from by simpa using hzz'); exact ⟨hz', by simpa using hu, by simpa using h⟩
      · simp [qqBvar, qqFvar] at h
      · simp [qqBvar, qqFunc] at h,
   by rintro ⟨hz, Hu, h⟩; exact Subst.bvar hz Hu h⟩

@[simp] lemma Subst.fvar {n m w x : M} :
    Subst L n m w ⟪^&x, ^&x⟫ := Subst.mk ⟨by simp, by simp, Or.inr <| Or.inl ⟨x, by simp⟩⟩

lemma Subst.fvar_iff {n m w x u : M} :
    Subst L n m w ⟪^&x, u⟫ ↔ u = ^&x := by
  constructor
  · intro h
    rcases h.case with ⟨_, _, (⟨_, _, h, _⟩ | ⟨x', hx', h⟩ | ⟨_, _, _, _, h, _⟩)⟩
    · simp [qqBvar, qqFvar] at h
    · rcases (show x = x' from by simpa using hx'); simpa using h
    · simp [qqFvar, qqFunc] at h
  · rintro rfl; simp

lemma Subst.func {n m w k f v v' : M}
    (hkf : L.Func k f)
    (Sv : Seq v)
    (hk : k = lh v)
    (hv : ∀ i u, ⟪i, u⟫ ∈ v → L.IsSemiterm n u)
    (Sv' : Seq v')
    (hk' : k = lh v')
    (hv' : ∀ i u', ⟪i, u'⟫ ∈ v' → L.IsSemiterm m u')
    (H : ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Subst L n m w ⟪u, u'⟫) :
    Subst L n m w ⟪^func k f v, ^func k f v'⟫ :=
  Subst.mk ⟨
    by rw [pi₁_pair]; exact IsSemiterm.func hkf Sv hk hv,
    by rw [pi₂_pair]; exact IsSemiterm.func hkf Sv' hk' hv',
    Or.inr <| Or.inr ⟨k, f, v, v', by simp, by simp, H⟩⟩

lemma Subst.func' {n m w k f v u : M} (h : Subst L n m w ⟪^func k f v, u⟫) :
    ∃ v', Seq v' ∧ k = lh v' ∧ (∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Subst L n m w ⟪u, u'⟫) ∧ u = ^func k f v' := by
  rcases h.case with ⟨_, hu, (⟨_, _, h, _⟩ | ⟨x, h, _⟩ | ⟨k', f', v', v'', h₁, h₂, hv⟩)⟩
  · simp [qqFunc, qqBvar] at h
  · simp [qqFunc, qqFvar] at h
  · rcases (show k = k' ∧ f = f' ∧ v = v' by simpa [qqFunc] using h₁) with ⟨rfl, rfl, rfl⟩
    rcases (show u = ^func k f v'' by simpa using h₂)
    have : L.Func k f ∧ Seq v'' ∧ k = lh v'' ∧ ∀ i u, ⟪i, u⟫ ∈ v'' → L.IsSemiterm m u := by simpa [IsSemiterm.func_iff] using hu
    rcases this with ⟨_, Sv'', hk'', _⟩
    exact ⟨v'', Sv'', hk'', hv, rfl⟩

variable {n m w} (TSw : TermSeq L n m w)

lemma Subst.rng_exists {t : M} (ht : L.IsSemiterm n t) : ∃ u, Subst L n m w ⟪t, u⟫ := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    have : ∃ u, ⟪z, u⟫ ∈ w := TSw.seq.exists (show z < lh w by simpa [TSw.lh] using hz)
    rcases this with ⟨u, hu⟩
    exact ⟨u, Subst.bvar hz (TSw.prop z u hu) hu⟩
  · intro x; exact ⟨^&x, by simp⟩
  · rintro k f v hkf Sv rfl ih
    have : ∃ v', Seq v' ∧ lh v' = lh v ∧ ∀ i u', ⟪i, u'⟫ ∈ v' → ∀ u, ⟪i, u⟫ ∈ v → Subst L n m w ⟪u, u'⟫ := by
      have : ∀ i < lh v, ∃ u', ∀ u, ⟪i, u⟫ ∈ v → Subst L n m w ⟪u, u'⟫ := by
        intro i hi
        have : L.IsSemiterm n (Sv.nth hi) ∧ ∃ u, Subst L n m w ⟪Sv.nth hi, u⟫ := ih i (Sv.nth hi) (by simp)
        rcases this with ⟨_, u', hu'⟩
        exact ⟨u', fun u hiuv  ↦ by rcases Sv.nth_uniq hi hiuv; exact hu'⟩
      exact sigmaOne_skolem_seq
        (by have : 𝚺₁-Relation fun x y ↦ ∀ u < v, ⟪x, u⟫ ∈ v → Subst L n m w ⟪u, y⟫ := by definability
            exact this.of_iff fun w ↦ ⟨fun h u _ ↦ h u, fun h u hv ↦ h u (lt_of_mem_rng hv) hv⟩)
        this
    rcases this with ⟨v', Sv', hvv', h⟩
    exact ⟨^func (lh v) f v',
      Subst.func hkf Sv rfl (fun i u hi ↦ (ih i u hi).1) Sv' (Eq.symm hvv')
        (fun i u' hi ↦ by
          have : i < lh v := by simpa [hvv'] using Sv'.lt_lh_of_mem hi
          exact h i u' hi (Sv.nth this) (by simp) |>.semiterm₂)
        (fun i u u' hi hi' ↦ h i u' hi' u hi)⟩

lemma Subst.rng_unique
    {t u₁ u₂ : M} : Subst L n m w ⟪t, u₁⟫ → Subst L n m w ⟪t, u₂⟫ → u₁ = u₂ := by
  revert u₁ u₂
  suffices L.IsSemiterm n t → ∀ u₁ u₂, Subst L n m w ⟪t, u₁⟫ → Subst L n m w ⟪t, u₂⟫ → u₁ = u₂
  by intro u₁ u₂ h₁ h₂; exact this h₁.semiterm₁ u₁ u₂ h₁ h₂
  intro ht
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · simp only [bvar_iff, and_imp]
    intro z _ u₁ u₂ _ _ h₁ _ _ h₂
    exact TSw.seq.isMapping.uniq h₁ h₂
  · simp [Subst.fvar_iff]
  · intro k f v _ Sv hk ih u₁ u₂ h₁ h₂
    rcases Subst.func' h₁ with ⟨v₁, Sv₁, hk₁, hvv₁, rfl⟩
    rcases Subst.func' h₂ with ⟨v₂, Sv₂, hk₂, hvv₂, rfl⟩
    have : v₁ = v₂ := Sv₁.lh_ext Sv₂ (by simp [←hk₁, ←hk₂]) (by
      intro i x₁ x₂ hxv₁ hxv₂
      have hi : i < lh v := by simpa [←hk, hk₁] using Sv₁.lt_lh_of_mem hxv₁
      exact ih i (Sv.nth hi) (by simp) |>.2 _ _ (hvv₁ _ _ _ (Sv.nth_mem hi) hxv₁) (hvv₂ _ _ _ (Sv.nth_mem hi) hxv₂))
    rw [this]

lemma Subst.rng_exists_unique {t : M} (ht : L.IsSemiterm n t) : ∃! u, Subst L n m w ⟪t, u⟫ := by
  rcases Subst.rng_exists TSw ht with ⟨u, hu⟩
  exact ExistsUnique.intro u hu (fun u' hu' ↦ Subst.rng_unique TSw hu' hu)

variable (L)

lemma Subst.rng_exists_unique_total (n m w t : M) :
    ∃! u, (TermSeq L n m w ∧ L.IsSemiterm n t → Subst L n m w ⟪t, u⟫) ∧ (¬(TermSeq L n m w ∧ L.IsSemiterm n t) → u = 0) := by
  by_cases h : TermSeq L n m w ∧ L.IsSemiterm n t
  · simp [h]; exact Subst.rng_exists_unique h.1 h.2
  · simp [h]

end FormalizedTermSubst

open FormalizedTermSubst

variable (L)

def Language.termSubst (n m w t : M) : M := Classical.choose! (Subst.rng_exists_unique_total L n m w t)

variable {L}

def TermSeq.spec_of_semiterm {n m w t : M} (TSw : TermSeq L n m w) (ht : L.IsSemiterm n t) : Subst L n m w ⟪t, L.termSubst n m w t⟫ :=
  Classical.choose!_spec (Subst.rng_exists_unique_total L n m w t) |>.1 ⟨TSw, ht⟩

def termSubst_spec {n m w t : M} :
    ¬(TermSeq L n m w ∧ L.IsSemiterm n t) → L.termSubst n m w t = 0 :=
  Classical.choose!_spec (Subst.rng_exists_unique_total L n m w t) |>.2

variable {n m w : M} (TSw : TermSeq L n m w)

lemma TermSeq.termSubst_eq_of {t} (ht : L.IsSemiterm n t) (h : Subst L n m w ⟪t, u⟫) : L.termSubst n m w t = u :=
  (TSw.spec_of_semiterm ht).rng_unique TSw h

lemma termSubst_bvar {z : M} (hz : z < n) (hu : ⟪z, u⟫ ∈ w) : L.termSubst n m w (^#z) = u :=
  TSw.termSubst_eq_of (by simp [hz]) (Subst.bvar hz (TSw.prop z u hu) hu)

@[simp] lemma termSubst_fvar (x : M) : L.termSubst n m w (^&x) = ^&x :=
  TSw.termSubst_eq_of (by simp) (by simp)

lemma termSubst_func {k f v v' : M} (hfk : L.Func k f)
    (Sv : Seq v) (hk : k = lh v) (hv : ∀ i u, ⟪i, u⟫ ∈ v → L.IsSemiterm n u)
    (Sv' : Seq v') (hk' : k = lh v') (hv' : ∀ i u', ⟪i, u'⟫ ∈ v' → L.IsSemiterm m u')
    (H : ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → L.termSubst n m w u = u') : L.termSubst n m w (^func k f v) = ^func k f v' :=
  TSw.termSubst_eq_of (IsSemiterm.func hfk Sv hk hv)
    (Subst.func hfk Sv hk hv Sv' hk' hv' (fun i u u' hi hi' ↦ by
      rcases H i u u' hi hi'; exact TermSeq.spec_of_semiterm TSw (hv i u hi)))

section

variable (L)

private lemma termSubst_graph (u n m w t : M) :
    u = L.termSubst n m w t ↔
    (TermSeq L n m w ∧ L.IsSemiterm n t → ∃ p ≤ (t + u + 1)^2, p = ⟪t, u⟫ ∧ Subst L n m w p) ∧ (¬(TermSeq L n m w ∧ L.IsSemiterm n t) → u = 0) :=
  Iff.trans (Classical.choose!_eq_iff (Subst.rng_exists_unique_total L n m w t)) ⟨by
    rintro ⟨hp, hn⟩
    exact ⟨fun h ↦ ⟨⟪t, u⟫, by simp, rfl, hp h⟩, hn⟩, by
    rintro ⟨hp, hn⟩
    exact ⟨fun h ↦ by rcases hp h with ⟨_, _, rfl, h⟩; exact h, hn⟩⟩

def _root_.LO.FirstOrder.Arith.LDef.termSubstDef (pL : LDef) : 𝚺₁-Semisentence 5 := .mkSigma
  “u n m w t | (!pL.termSeqDef.pi n m w ∧ !pL.isSemitermDef.pi n t → ∃ p <⁺ (t + u + 1)², !pairDef p t u ∧ !pL.substDef.sigma n m w p) ∧
    (¬(!pL.termSeqDef.sigma n m w ∧ !pL.isSemitermDef.sigma n t) → u = 0)” (by simp)

lemma termSubst_defined : DefinedFunction (fun v ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) pL.termSubstDef := by
  intro v
  simp [LDef.termSubstDef, termSubst_graph, HSemiformula.val_sigma, eval_termSeq L,
    eval_isSemitermDef L, (termSeq_defined L).proper.iff', (isSemiterm_defined L).proper.iff', eval_substDef L, -and_imp, -not_and]
  apply iff_of_eq; congr; simp [imp_iff_not_or]; rfl

@[simp] lemma termSubst_defined_iff (v : Fin 5 → M) :
    Semiformula.Evalbm (L := ℒₒᵣ) M v pL.termSubstDef ↔ v 0 = L.termSubst (v 1) (v 2) (v 3) (v 4) := (termSubst_defined L).df.iff v

instance termSubst_definable : DefinableFunction ℒₒᵣ 𝚺₁ (fun v : Fin 4 → M ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) :=
  Defined.to_definable _ (termSubst_defined L)

end

end termSubst

section termShift

namespace FormalizedTermShift

variable (L)

def Phi (n : M) (C : Set M) (p : M) : Prop :=
  L.IsSemiterm n (π₁ p) ∧ L.IsSemiterm n (π₂ p) ∧
  ( (∃ z < n, π₁ p = ^#z ∧ π₂ p = ^#z) ∨
    (∃ x, π₁ p = ^&x ∧ π₂ p = ^&(x + 1)) ∨
    (∃ k f v v', π₁ p = ^func k f v ∧ π₂ p = ^func k f v' ∧ ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → ⟪u, u'⟫ ∈ C) )

private lemma phi_iff (n C p : M) :
    Phi L n {x | x ∈ C} p ↔
    ∃ t₁ ≤ p, ∃ t₂ ≤ p, p = ⟪t₁, t₂⟫ ∧ L.IsSemiterm n t₁ ∧ L.IsSemiterm n t₂ ∧
    ( (∃ z < n, t₁ = ^#z ∧ t₂ = ^#z) ∨
      (∃ x < t₁, t₁ = ^&x ∧ t₂ = ^&(x + 1)) ∨
      (∃ k < t₁, ∃ f < t₁, ∃ v < t₁, ∃ v' < t₂, t₁ = ^func k f v ∧ t₂ = ^func k f v' ∧
        (∀ i < v, ∀ u < v, ∀ u' < v', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → ⟪u, u'⟫ ∈ C)) ) := by
  constructor
  ·{intro ⟨hp₁, hp₂, h⟩
    refine ⟨π₁ p, by simp, π₂ p, by simp, by simp, hp₁, hp₂, ?_⟩
    rcases h with (⟨z, hz, h₁, h⟩ | ⟨x, h₁, h₂⟩ | ⟨k, f, v, v', h₁, h₂, h⟩)
    · left; exact ⟨z, hz, h₁, h⟩
    · right; left; exact ⟨x, by simp [h₁], h₁, h₂⟩
    · right; right
      exact ⟨k, by simp [h₁], f, by simp [h₁], v, by simp [h₁], v', by simp [h₂],
        h₁, h₂, fun i _ u _ u' _ hi hi' ↦ h i u u' hi hi'⟩}
  · rintro ⟨t₁, _, t₂, _, rfl, ht₁, ht₂, h⟩
    refine ⟨by simpa using ht₁, by simpa using ht₂, ?_⟩
    rcases h with (⟨z, hz, rfl, h⟩ | ⟨x, _, rfl, rfl⟩ | ⟨k, _, f, _, v, _, v', _, rfl, rfl, h⟩)
    · left; exact ⟨z, hz, by simp [h]⟩
    · right; left; exact ⟨x, by simp⟩
    · right; right
      exact ⟨k, f, v, v', by simp, by simp, fun i u u' hi hi' ↦
        h i (lt_of_mem_dom hi) u (lt_of_mem_rng hi) u' (lt_of_mem_rng hi') hi hi'⟩

def formulaAux : Semisentence ℒₒᵣ 5 := “t₁ t₂ p C n |
  (∃ z < n, !qqBvarDef t₁ z ∧ !qqBvarDef t₂ z) ∨
  (∃ x < t₁, !qqFvarDef t₁ x ∧ !qqFvarDef t₂ (x + 1)) ∨
  (∃ k < t₁, ∃ f < t₁, ∃ v < t₁, ∃ v' < t₂, !qqFuncDef t₁ k f v ∧ !qqFuncDef t₂ k f v' ∧
  (∀ i < v, ∀ u < v, ∀ u' < v', i ~[v] u → i ~[v'] u' → u ~[C] u'))”

def formula (pL : LDef) : Fixpoint.Formula 1 := ⟨.mkDelta
  (.mkSigma
    “p C n |
      ∃ t₁ <⁺ p, ∃ t₂ <⁺ p, !pairDef p t₁ t₂ ∧ !pL.isSemitermDef.sigma n t₁ ∧ !pL.isSemitermDef.sigma n t₂ ∧
      !formulaAux t₁ t₂ p C n”
    (by simp [formulaAux]))
  (.mkPi
    “p C n |
      ∃ t₁ <⁺ p, ∃ t₂ <⁺ p, !pairDef p t₁ t₂ ∧ !pL.isSemitermDef.pi n t₁ ∧ !pL.isSemitermDef.pi n t₂ ∧
      !formulaAux t₁ t₂ p C n”
    (by simp [formulaAux]))⟩

def construction : Fixpoint.Construction M (formula pL) where
  Φ := fun v ↦ Phi L (v 0)
  defined := ⟨fun v ↦
    by simp [formula, HSemiformula.val_sigma, eval_isSemitermDef L, (isSemiterm_defined L).proper.iff'],
  fun v ↦ by simpa [formula, HSemiformula.val_sigma, eval_isSemitermDef L, formulaAux] using phi_iff _ _ _ _⟩
  monotone := by
    rintro C C' hC v p ⟨ht₁, ht₂, (h | h | ⟨k, f, v, v', h₁, h₂, h⟩)⟩
    · exact ⟨ht₁, ht₂, Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inr ⟨k, f, v, v', h₁, h₂, fun i u u' hi hi' ↦ hC (h i u u' hi hi')⟩⟩
  finite := by
    rintro C v p ⟨ht₁, ht₂, (h | h | ⟨k, f, v, v', h₁, h₂, h⟩)⟩
    · exact ⟨ht₁, ht₂, Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inl h⟩
    · exact ⟨ht₁, ht₂, Or.inr <| Or.inr ⟨k, f, v, v', h₁, h₂, fun i u u' hi hi' ↦ ⟨h i u u' hi hi', by
      have : ⟪u, u'⟫ < ⟪π₁ p, π₂ p⟫ := pair_lt_pair (by simpa [h₁] using lt_qqFunc_of_mem hi) (by simpa [h₂] using lt_qqFunc_of_mem hi')
      simpa using this⟩⟩⟩

def Shift (n : M) : M → Prop := (construction L).Fixpoint ![n]

def shiftDef (pL : LDef) : 𝚫₁-Semisentence 2 := (formula pL).fixpointDef.rew <| Rew.substs ![#1, #0]

lemma shift_defined : 𝚫₁-Relation (Shift L) via (shiftDef pL) :=
  ⟨HSemiformula.ProperOn.rew (construction L).fixpoint_defined.proper _,
   by intro v; simp [shiftDef, (construction L).eval_fixpointDef, Shift]⟩

@[simp] lemma eval_shiftDef (v) :
    Semiformula.Evalbm M v (shiftDef pL).val ↔ Shift L (v 0) (v 1) := (shift_defined L).df.iff v

instance shift_definable : 𝚫₁-Relation (Shift L) := Defined.to_definable _ (shift_defined L)

@[simp, definability] instance shift_definable' (Γ) : (Γ, m + 1)-Relation (Shift L) :=
  .of_deltaOne (shift_definable L) _ _

variable {L}

lemma Shift.case_iff {n p : M} :
    Shift L n p ↔
    L.IsSemiterm n (π₁ p) ∧ L.IsSemiterm n (π₂ p) ∧
    ( (∃ z < n, π₁ p = ^#z ∧ π₂ p = ^#z) ∨
      (∃ x, π₁ p = ^&x ∧ π₂ p = ^&(x + 1)) ∨
      (∃ k f v v', π₁ p = ^func k f v ∧ π₂ p = ^func k f v' ∧ ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Shift L n ⟪u, u'⟫) ) :=
  (construction L).case

alias ⟨Shift.case, Shift.mk⟩ := Shift.case_iff

lemma Shift.semiterm₁ {n t t'} (h : Shift L n ⟪t, t'⟫) : L.IsSemiterm n t := by simpa using h.case.1

lemma Shift.semiterm₂ {n t t'} (h : Shift L n ⟪t, t'⟫) : L.IsSemiterm n t' := by simpa using h.case.2.1

@[simp] lemma Shift.bvar {n z : M} (hz : z < n) :
    Shift L n ⟪^#z, ^#z⟫ := Shift.mk ⟨by simp [hz], by simp [hz]⟩

lemma Shift.bvar_iff {n z u : M} :
    Shift L n ⟪^#z, u⟫ ↔ z < n ∧ u = ^#z :=
  ⟨by intro h
      rcases h.case with ⟨_, _, (⟨z', hz', hzz', h⟩ | ⟨x, h, _⟩ | ⟨k, f, v, v', h, _⟩)⟩
      · rcases (show z = z' from by simpa using hzz'); exact ⟨hz', by simpa using h⟩
      · simp [qqBvar, qqFvar] at h
      · simp [qqBvar, qqFunc] at h,
   by rintro ⟨hz, Hu, h⟩; exact Shift.bvar hz⟩

@[simp] lemma Shift.fvar {n : M} (x : M):
    Shift L n ⟪^&x, ^&(x + 1)⟫ := Shift.mk ⟨by simp, by simp⟩

lemma Shift.fvar_iff {n x u : M} :
    Shift L n ⟪^&x, u⟫ ↔ u = ^&(x + 1) :=
  ⟨by intro h
      rcases h.case with ⟨_, _, (⟨_, _, h, _⟩ | ⟨x', hx', h⟩ | ⟨_, _, _, _, h, _, _⟩)⟩
      · simp [qqBvar, qqFvar] at h
      · rcases (show x = x' by simpa using hx'); simpa using h
      · simp [qqFvar, qqFunc] at h,
   by rintro ⟨hz, Hu, h⟩; exact Shift.fvar x⟩

lemma Shift.func {n k f v v' : M}
    (hkf : L.Func k f)
    (Sv : Seq v)
    (hk : k = lh v)
    (hv : ∀ i u, ⟪i, u⟫ ∈ v → L.IsSemiterm n u)
    (Sv' : Seq v')
    (hk' : k = lh v')
    (hv' : ∀ i u', ⟪i, u'⟫ ∈ v' → L.IsSemiterm n u')
    (H : ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Shift L n ⟪u, u'⟫) :
    Shift L n ⟪^func k f v, ^func k f v'⟫ :=
  Shift.mk ⟨
    by rw [pi₁_pair]; exact IsSemiterm.func hkf Sv hk hv,
    by rw [pi₂_pair]; exact IsSemiterm.func hkf Sv' hk' hv',
    Or.inr <| Or.inr ⟨k, f, v, v', by simp, by simp, H⟩⟩

lemma Shift.func' {n k f v u : M} (h : Shift L n ⟪^func k f v, u⟫) :
    ∃ v', Seq v' ∧ k = lh v' ∧ (∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → Shift L n ⟪u, u'⟫) ∧ u = ^func k f v' := by
  rcases h.case with ⟨_, hu, (⟨_, _, h, _⟩ | ⟨x, h, _⟩ | ⟨k', f', v', v'', h₁, h₂, hv⟩)⟩
  · simp [qqFunc, qqBvar] at h
  · simp [qqFunc, qqFvar] at h
  · rcases (show k = k' ∧ f = f' ∧ v = v' by simpa [qqFunc] using h₁) with ⟨rfl, rfl, rfl⟩
    rcases (show u = ^func k f v'' by simpa using h₂)
    have : L.Func k f ∧ Seq v'' ∧ k = lh v'' ∧ ∀ i u, ⟪i, u⟫ ∈ v'' → L.IsSemiterm n u := by simpa [IsSemiterm.func_iff] using hu
    rcases this with ⟨_, Sv'', hk'', _⟩
    exact ⟨v'', Sv'', hk'', hv, rfl⟩

variable {n : M}

lemma Shift.rng_exists {t : M} (ht : L.IsSemiterm n t) : ∃ u, Shift L n ⟪t, u⟫ := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; exact ⟨^#z, Shift.bvar hz⟩
  · intro x; exact ⟨^&(x + 1), by simp⟩
  · rintro k f v hkf Sv rfl ih
    have : ∃ v', Seq v' ∧ lh v' = lh v ∧ ∀ i u', ⟪i, u'⟫ ∈ v' → ∀ u, ⟪i, u⟫ ∈ v → Shift L n ⟪u, u'⟫ := by
      have : ∀ i < lh v, ∃ u', ∀ u, ⟪i, u⟫ ∈ v → Shift L n ⟪u, u'⟫ := by
        intro i hi
        have : L.IsSemiterm n (Sv.nth hi) ∧ ∃ u, Shift L n ⟪Sv.nth hi, u⟫ := ih i (Sv.nth hi) (by simp)
        rcases this with ⟨_, u', hu'⟩
        exact ⟨u', fun u hiuv  ↦ by rcases Sv.nth_uniq hi hiuv; exact hu'⟩
      exact sigmaOne_skolem_seq
        (by have : 𝚺₁-Relation fun x y ↦ ∀ u < v, ⟪x, u⟫ ∈ v → Shift L n ⟪u, y⟫ := by definability
            exact this.of_iff fun w ↦ ⟨fun h u _ ↦ h u, fun h u hv ↦ h u (lt_of_mem_rng hv) hv⟩)
        this
    rcases this with ⟨v', Sv', hvv', h⟩
    exact ⟨^func (lh v) f v',
      Shift.func hkf Sv rfl (fun i u hi ↦ (ih i u hi).1) Sv' (Eq.symm hvv')
        (fun i u' hi ↦ by
          have : i < lh v := by simpa [hvv'] using Sv'.lt_lh_of_mem hi
          exact h i u' hi (Sv.nth this) (by simp) |>.semiterm₂)
        (fun i u u' hi hi' ↦ h i u' hi' u hi)⟩

lemma Shift.rng_unique
    {t u₁ u₂ : M} : Shift L n ⟪t, u₁⟫ → Shift L n ⟪t, u₂⟫ → u₁ = u₂ := by
  revert u₁ u₂
  suffices L.IsSemiterm n t → ∀ u₁ u₂, Shift L n ⟪t, u₁⟫ → Shift L n ⟪t, u₂⟫ → u₁ = u₂
  by intro u₁ u₂ h₁ h₂; exact this h₁.semiterm₁ u₁ u₂ h₁ h₂
  intro ht
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · simp only [bvar_iff, and_imp]
    rintro z _ u₁ u₂ _ rfl _ rfl; rfl
  · simp [Shift.fvar_iff]
  · intro k f v _ Sv hk ih u₁ u₂ h₁ h₂
    rcases Shift.func' h₁ with ⟨v₁, Sv₁, hk₁, hvv₁, rfl⟩
    rcases Shift.func' h₂ with ⟨v₂, Sv₂, hk₂, hvv₂, rfl⟩
    have : v₁ = v₂ := Sv₁.lh_ext Sv₂ (by simp [←hk₁, ←hk₂]) (by
      intro i x₁ x₂ hxv₁ hxv₂
      have hi : i < lh v := by simpa [←hk, hk₁] using Sv₁.lt_lh_of_mem hxv₁
      exact ih i (Sv.nth hi) (by simp) |>.2 _ _ (hvv₁ _ _ _ (Sv.nth_mem hi) hxv₁) (hvv₂ _ _ _ (Sv.nth_mem hi) hxv₂))
    rw [this]

lemma Shift.rng_exists_unique {t : M} (ht : L.IsSemiterm n t) : ∃! u, Shift L n ⟪t, u⟫ := by
  rcases Shift.rng_exists ht with ⟨u, hu⟩
  exact ExistsUnique.intro u hu (fun u' hu' ↦ Shift.rng_unique hu' hu)

variable (L)

lemma Shift.rng_exists_unique_total (n t : M) :
    ∃! u, (L.IsSemiterm n t → Shift L n ⟪t, u⟫) ∧ (¬L.IsSemiterm n t → u = 0) := by
  by_cases h : L.IsSemiterm n t
  · simp [h]; exact Shift.rng_exists_unique h
  · simp [h]

end FormalizedTermShift

open FormalizedTermShift

variable (L)

def Language.termShift (n t : M) : M := Classical.choose! (Shift.rng_exists_unique_total L n t)

variable {L}

lemma Language.IsSemiterm.termShift_spec {n t : M} (ht : L.IsSemiterm n t) : Shift L n ⟪t, L.termShift n t⟫ :=
  Classical.choose!_spec (Shift.rng_exists_unique_total L n t) |>.1 ht

lemma termShift_spec_of_not_termShift {n t : M} :
    ¬L.IsSemiterm n t → L.termShift n t = 0 :=
  Classical.choose!_spec (Shift.rng_exists_unique_total L n t) |>.2

lemma Language.IsSemiterm.termShift_eq_of {n t} (ht : L.IsSemiterm n t) (h : Shift L n ⟪t, u⟫) : L.termShift n t = u :=
  ht.termShift_spec.rng_unique h

lemma termShift_bvar {z : M} (hz : z < n) : L.termShift n (^#z) = ^#z :=
  Language.IsSemiterm.termShift_eq_of (by simp [hz]) (Shift.bvar hz)

@[simp] lemma termShift_fvar (x : M) : L.termShift n (^&x) = ^&(x + 1) :=
  Language.IsSemiterm.termShift_eq_of (by simp) (Shift.fvar x)

lemma termShift_func {k f v v' : M} (hfk : L.Func k f)
    (Sv : Seq v) (hk : k = lh v) (hv : ∀ i u, ⟪i, u⟫ ∈ v → L.IsSemiterm n u)
    (Sv' : Seq v') (hk' : k = lh v') (hv' : ∀ i u', ⟪i, u'⟫ ∈ v' → L.IsSemiterm n u')
    (H : ∀ i u u', ⟪i, u⟫ ∈ v → ⟪i, u'⟫ ∈ v' → L.termShift n u = u') : L.termShift n (^func k f v) = ^func k f v' :=
  Language.IsSemiterm.termShift_eq_of (IsSemiterm.func hfk Sv hk hv)
    (Shift.func hfk Sv hk hv Sv' hk' hv' (fun i u u' hi hi' ↦ by
      rcases H i u u' hi hi'
      exact Language.IsSemiterm.termShift_spec (hv i u hi)))

section

variable (L)

private lemma termShift_graph (u n t : M) :
    u = L.termShift n t ↔
    (L.IsSemiterm n t → ∃ p ≤ (t + u + 1)^2, p = ⟪t, u⟫ ∧ Shift L n p) ∧ (¬L.IsSemiterm n t → u = 0) :=
  Iff.trans (Classical.choose!_eq_iff (Shift.rng_exists_unique_total L n t)) ⟨by
    rintro ⟨hp, hn⟩
    exact ⟨fun h ↦ ⟨⟪t, u⟫, by simp, rfl, hp h⟩, hn⟩, by
    rintro ⟨hp, hn⟩
    exact ⟨fun h ↦ by rcases hp h with ⟨_, _, rfl, h⟩; exact h, hn⟩⟩

def _root_.LO.FirstOrder.Arith.LDef.termShiftDef (pL : LDef) : 𝚺₁-Semisentence 3 := .mkSigma
  “u n t | (!pL.isSemitermDef.pi n t → ∃ p <⁺ (t + u + 1)², !pairDef p t u ∧ !(shiftDef pL).sigma n p) ∧ (¬!pL.isSemitermDef.sigma n t → u = 0)” (by simp)

lemma termShift_defined : 𝚺₁-Function₂ L.termShift via pL.termShiftDef := by
  intro v
  simp [LDef.termShiftDef, termShift_graph, HSemiformula.val_sigma, eval_termSeq L,
    eval_isSemitermDef L, (termSeq_defined L).proper.iff', (isSemiterm_defined L).proper.iff', eval_shiftDef L, -and_imp, -not_and]

@[simp] lemma termShift_defined_iff (v : Fin 3 → M) :
    Semiformula.Evalbm (L := ℒₒᵣ) M v pL.termShiftDef ↔ v 0 = L.termShift (v 1) (v 2) := (termShift_defined L).df.iff v

instance termShift_definable : 𝚺₁-Function₂ L.termShift :=
  Defined.to_definable _ (termShift_defined L)

end

end termShift

end LO.FirstOrder.Arith.Model

end
