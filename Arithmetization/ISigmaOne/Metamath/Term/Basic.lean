import Arithmetization.ISigmaOne.Metamath.Language
import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section term

def qqBvar (z : V) : V := ⟪0, z⟫ + 1

def qqFvar (x : V) : V := ⟪1, x⟫ + 1

def qqFunc (k f v : V) : V := ⟪2, k, f, v⟫ + 1

scoped prefix:max "^#" => qqBvar

scoped prefix:max "^&" => qqFvar

scoped prefix:max "^func " => qqFunc

@[simp] lemma var_lt_qqBvar (z : V) : z < ^#z := lt_succ_iff_le.mpr <| le_pair_right 0 z

@[simp] lemma var_lt_qqFvar (x : V) : x < ^&x := lt_succ_iff_le.mpr <| le_pair_right 1 x

@[simp] lemma arity_lt_qqFunc (k f v : V) : k < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right 2 k) <| pair_le_pair_right 2 <| le_pair_left k ⟪f, v⟫

@[simp] lemma func_lt_qqFunc (k f v : V) : f < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

@[simp] lemma terms_lt_qqFunc (k f v : V) : v < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right f v) <| le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

lemma nth_lt_qqFunc_of_lt {i k f v : V} (hi : i < len v) : v.[i] < ^func k f v :=
  lt_trans (nth_lt_self hi) (terms_lt_qqFunc _ _ _)

@[simp] lemma qqBvar_inj {z z' : V} : ^#z = ^#z' ↔ z = z' := by simp [qqBvar]

@[simp] lemma qqFvar_inj {x x' : V} : ^&x = ^&x' ↔ x = x' := by simp [qqFvar]

@[simp] lemma qqFunc_inj {k f v k' f' w : V} : ^func k f v = ^func k' f' w ↔ k = k' ∧ f = f' ∧ v = w := by simp [qqFunc]

def _root_.LO.FirstOrder.Arith.qqBvarDef : 𝚺₀.Semisentence 2 := .mkSigma “t z. ∃ t' < t, !pairDef t' 0 z ∧ t = t' + 1” (by simp)

lemma qqBvar_defined : 𝚺₀-Function₁ (qqBvar : V → V) via qqBvarDef := by
  intro v; simp [qqBvarDef]
  constructor
  · intro h; exact ⟨⟪0, v 1⟫, by simp [qqBvar, h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqBvarDef (v) :
    Semiformula.Evalbm V v qqBvarDef.val ↔ v 0 = ^#(v 1) := qqBvar_defined.df.iff v

def _root_.LO.FirstOrder.Arith.qqFvarDef : 𝚺₀.Semisentence 2 := .mkSigma “t x. ∃ t' < t, !pairDef t' 1 x ∧ t = t' + 1” (by simp)

lemma qqFvar_defined : 𝚺₀-Function₁ (qqFvar : V → V) via qqFvarDef := by
  intro v; simp [qqFvarDef]
  constructor
  · intro h; exact ⟨⟪1, v 1⟫, by simp [qqFvar, h], rfl, h⟩
  · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_qqFvarDef (v) :
    Semiformula.Evalbm V v qqFvarDef.val ↔ v 0 = ^&(v 1) := qqFvar_defined.df.iff v

private lemma qqFunc_graph {x k f v : V} :
    x = ^func k f v ↔ ∃ fv < x, fv = ⟪f, v⟫ ∧ ∃ kfv < x, kfv = ⟪k, fv⟫ ∧ ∃ x' < x, x' = ⟪2, kfv⟫ ∧ x = x' + 1 :=
  ⟨by rintro rfl
      exact ⟨⟪f, v⟫, lt_succ_iff_le.mpr <| le_trans (le_pair_right _ _) (le_pair_right _ _), rfl,
        ⟪k, f, v⟫, lt_succ_iff_le.mpr <| by simp, rfl,
        ⟪2, k, f, v⟫, by simp [qqFunc], rfl, rfl⟩,
   by rintro ⟨_, _, rfl, _, _, rfl, _, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arith.qqFuncDef : 𝚺₀.Semisentence 4 := .mkSigma
  “x k f v. ∃ fv < x, !pairDef fv f v ∧ ∃ kfv < x, !pairDef kfv k fv ∧ ∃ x' < x, !pairDef x' 2 kfv ∧ x = x' + 1” (by simp)

lemma qqFunc_defined : 𝚺₀-Function₃ (qqFunc : V → V → V → V) via qqFuncDef := by
  intro v; simp [qqFuncDef, qqFunc_graph]

@[simp] lemma eval_qqFuncDef (v) :
    Semiformula.Evalbm V v qqFuncDef.val ↔ v 0 = ^func (v 1) (v 2) (v 3) := qqFunc_defined.df.iff v

namespace FormalizedTerm

variable (L)

def Phi (C : Set V) (t : V) : Prop :=
  (∃ z, t = ^#z) ∨ (∃ x, t = ^&x) ∨ (∃ k f v : V, L.Func k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v)

private lemma phi_iff (C : V) (t : V) :
    Phi L {x | x ∈ C} t ↔
    (∃ z < t, t = ^#z) ∨
    (∃ x < t, t = ^&x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t, L.Func k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v) where
  mp := by
    rintro (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, hk, hv, rfl⟩)
    · left; exact ⟨z, lt_succ_iff_le.mpr <| by simp, rfl⟩
    · right; left
      exact ⟨x, lt_succ_iff_le.mpr <| by simp, rfl⟩
    · right; right
      exact ⟨k, by simp, f, by simp, v, by simp, hkf, hk, hv, rfl⟩
  mpr := by
    unfold Phi
    rintro (⟨z, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨k, _, f, _, v, _, hkf, hk, hv, rfl⟩)
    · left; exact ⟨z, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right; exact ⟨k, f, v, hkf, hk, hv, rfl⟩

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 where
  core := .mkDelta
    (.mkSigma “t C.
      (∃ z < t, !qqBvarDef t z) ∨
      (∃ x < t, !qqFvarDef t x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, !pL.func k f ∧ !lenDef k v ∧ (∀ i < k, ∃ u, !nthDef u v i ∧ u ∈ C) ∧ !qqFuncDef t k f v)”
    (by simp))
    (.mkPi “t C.
      (∃ z < t, !qqBvarDef t z) ∨
      (∃ x < t, !qqFvarDef t x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, !pL.func k f ∧ (∀ l, !lenDef l v → k = l) ∧ (∀ i < k, ∀ u, !nthDef u v i → u ∈ C) ∧ !qqFuncDef t k f v)”
    (by simp))

def construction : Fixpoint.Construction V (blueprint pL) where
  Φ := fun _ ↦ Phi L
  defined := ⟨by intro v; simp [blueprint], by
    intro v; simp [blueprint, phi_iff, Language.Defined.eval_func (L := L)]⟩
  monotone := by
    rintro C C' hC _ x (h | h | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · exact Or.inl h
    · exact Or.inr <| Or.inl h
    · exact Or.inr <| Or.inr ⟨k, f, v, hkf, hk, fun i hi ↦ hC (h i hi), rfl⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C v x (h | h | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · exact Or.inl h
    · exact Or.inr <| Or.inl h
    · exact Or.inr <| Or.inr ⟨k, f, v, hkf, hk, fun i hi ↦
        ⟨h i hi, lt_of_le_of_lt (nth_le _ _) (by simp)⟩, rfl⟩

end FormalizedTerm

open FormalizedTerm

variable (L)

def Language.IsUTerm : V → Prop := (construction L).Fixpoint ![]

def _root_.LO.FirstOrder.Arith.LDef.isUTermDef (pL : LDef) : 𝚫₁.Semisentence 1 := (blueprint pL).fixpointDefΔ₁

lemma Language.isUTerm_defined : 𝚫₁-Predicate L.IsUTerm via pL.isUTermDef := (construction L).fixpoint_definedΔ₁

@[simp] lemma eval_isUTermDef (v) :
    Semiformula.Evalbm V v pL.isUTermDef.val ↔ L.IsUTerm (v 0) := L.isUTerm_defined.df.iff v

instance Language.isUTerm_definable : 𝚫₁-Predicate L.IsUTerm := L.isUTerm_defined.to_definable

instance isUTermDef_definable' (Γ) : Γ-[m + 1]-Predicate L.IsUTerm := L.isUTerm_definable.of_deltaOne

def Language.IsUTermVec (n w : V) : Prop := n = len w ∧ ∀ i < n, L.IsUTerm w.[i]

variable {L}

protected lemma Language.IsUTermVec.lh {n w : V} (h : L.IsUTermVec n w) : n = len w := h.1

lemma Language.IsUTermVec.nth {n w : V} (h : L.IsUTermVec n w) {i} : i < n → L.IsUTerm w.[i] := h.2 i

@[simp] lemma Language.IsUTermVec.empty : L.IsUTermVec 0 0 := ⟨by simp, by simp⟩

@[simp] lemma Language.IsUTermVec.empty_iff : L.IsUTermVec 0 v ↔ v = 0 := by
  constructor
  · intro h; exact len_zero_iff_eq_nil.mp h.lh.symm
  · rintro rfl; simp

lemma Language.IsUTermVec.two_iff {v : V} : L.IsUTermVec 2 v ↔ ∃ t₁ t₂, L.IsUTerm t₁ ∧ L.IsUTerm t₂ ∧ v = ?[t₁, t₂] := by
  constructor
  · intro h
    rcases eq_doubleton_of_len_eq_two.mp h.lh.symm with ⟨t₁, t₂, rfl⟩
    exact ⟨t₁, t₂, by simpa using h.nth (show 0 < 2 by simp), by simpa using h.nth (show 1 < 2 by simp), rfl⟩
  · rintro ⟨t₁, t₂, h₁, h₂, rfl⟩; exact ⟨by simp [one_add_one_eq_two], by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h₁, h₂]⟩

@[simp] lemma Language.IsUTermVec.cons {n w t : V} (h : L.IsUTermVec n w) (ht : L.IsUTerm t) : L.IsUTermVec (n + 1) (t ∷ w) :=
  ⟨by simp [h.lh], fun i hi ↦ by
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simpa
    · simpa using h.nth (by simpa using hi)⟩

@[simp] lemma Language.IsUTermVec.cons₁_iff {t : V} :
    L.IsUTermVec 1 ?[t] ↔ L.IsUTerm t := by
  constructor
  · intro h; simpa using h.nth (i := 0) (by simp)
  · intro h; simpa using Language.IsUTermVec.empty.cons h

@[simp] lemma Language.IsUTermVec.mkSeq₂_iff {t₁ t₂ : V} :
    L.IsUTermVec 2 ?[t₁, t₂] ↔ L.IsUTerm t₁ ∧ L.IsUTerm t₂ := by
  constructor
  · intro h; exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨h₁, h₂⟩
    simpa [one_add_one_eq_two] using (Language.IsUTermVec.cons₁_iff.mpr h₂).cons h₁

section

def _root_.LO.FirstOrder.Arith.LDef.isUTermVecDef (pL : LDef) : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma
    “n w. !lenDef n w ∧ ∀ i < n, ∃ u, !nthDef u w i ∧ !pL.isUTermDef.sigma u”
    (by simp))
  (.mkPi
    “n w. (∀ l, !lenDef l w → n = l) ∧ ∀ i < n, ∀ u, !nthDef u w i → !pL.isUTermDef.pi u”
    (by simp))

variable (L)

lemma Language.isUTermVec_defined : 𝚫₁-Relation L.IsUTermVec via pL.isUTermVecDef :=
  ⟨by intro v; simp [LDef.isUTermVecDef, HierarchySymbol.Semiformula.val_sigma, eval_isUTermDef L, L.isUTerm_defined.proper.iff'],
   by intro v; simp [LDef.isUTermVecDef, HierarchySymbol.Semiformula.val_sigma, eval_isUTermDef L, Language.IsUTermVec]⟩

@[simp] lemma eval_isUTermVecDef (v) :
    Semiformula.Evalbm V v pL.isUTermVecDef.val ↔ L.IsUTermVec (v 0) (v 1) := L.isUTermVec_defined.df.iff v

instance Language.isUTermVecDef_definable : 𝚫₁-Relation (L.IsUTermVec) := L.isUTermVec_defined.to_definable

instance Language.isUTermVecDef_definable' (Γ) : Γ-[m + 1]-Relation L.IsUTermVec := L.isUTermVecDef_definable.of_deltaOne

end

lemma Language.IsUTerm.case_iff {t : V} :
    L.IsUTerm t ↔
    (∃ z, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.Func k f ∧ L.IsUTermVec k v ∧ t = ^func k f v) := by
  simpa [construction, Phi, IsUTermVec, and_assoc] using (construction L).case

alias ⟨Language.IsUTerm.case, Language.IsUTerm.mk⟩ := Language.IsUTerm.case_iff

@[simp] lemma Language.IsUTerm.bvar {z : V} : L.IsUTerm ^#z :=
  Language.IsUTerm.mk (Or.inl ⟨z, rfl⟩)

@[simp] lemma Language.IsUTerm.fvar (x : V) : L.IsUTerm ^&x :=
  Language.IsUTerm.mk (Or.inr <| Or.inl ⟨x, rfl⟩)

@[simp] lemma Language.IsUTerm.func_iff {k f v : V} :
    L.IsUTerm (^func k f v) ↔ L.Func k f ∧ L.IsUTermVec k v :=
  ⟨by intro h
      rcases h.case with (⟨_, h⟩ | ⟨x, h⟩ | ⟨k', f', w, hkf, ⟨hk, hv⟩, h⟩)
      · simp [qqFunc, qqBvar] at h
      · simp [qqFunc, qqFvar] at h
      · rcases (show k = k' ∧ f = f' ∧ v = w by simpa [qqFunc] using h) with ⟨rfl, rfl, rfl⟩
        exact ⟨hkf, hk, hv⟩,
   by rintro ⟨hkf, hk, hv⟩; exact Language.IsUTerm.mk (Or.inr <| Or.inr ⟨k, f, v, hkf, ⟨hk, hv⟩, rfl⟩)⟩

lemma Language.IsUTerm.func {k f v : V} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    L.IsUTerm (^func k f v) := Language.IsUTerm.func_iff.mpr ⟨hkf, hv⟩

lemma Language.IsUTerm.induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hbvar : ∀ z, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.Func k f → L.IsUTermVec k v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, L.IsUTerm t → P t :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · exact hbvar z
    · exact hfvar x
    · exact hfunc k f v hkf ⟨hk, fun i hi ↦ hC _ (h i hi) |>.1⟩ (fun i hi ↦ hC _ (h i hi) |>.2))

end term

namespace Language.TermRec

structure Blueprint (pL : LDef) (arity : ℕ) where
  bvar : 𝚺₁.Semisentence (arity + 2)
  fvar : 𝚺₁.Semisentence (arity + 2)
  func : 𝚺₁.Semisentence (arity + 5)

namespace Blueprint

variable (β : Blueprint pL arity)

def blueprint : Fixpoint.Blueprint arity := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ t <⁺ pr, ∃ y <⁺ pr, !pairDef pr t y ∧ !pL.isUTermDef.sigma t ∧
    ( (∃ z < t, !qqBvarDef t z ∧ !β.bvar y z ⋯) ∨
      (∃ x < t, !qqFvarDef t x ∧ !β.fvar y x ⋯) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∃ rv, !repeatVecDef rv C k ∧ ∃ w <⁺ rv,
        (!lenDef k w ∧ ∀ i < k, ∃ vi, !nthDef vi v i ∧ ∃ v'i, !nthDef v'i w i ∧ :⟪vi, v'i⟫:∈ C) ∧
        !qqFuncDef t k f v ∧ !β.func y k f v w ⋯) )”
    (by simp))
  (.mkPi “pr C.
    ∃ t <⁺ pr, ∃ y <⁺ pr, !pairDef pr t y ∧ !pL.isUTermDef.pi t ∧
    ( (∃ z < t, !qqBvarDef t z ∧ !β.bvar.graphDelta.pi y z ⋯) ∨
      (∃ x < t, !qqFvarDef t x ∧ !β.fvar.graphDelta.pi y x ⋯) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∀ rv, !repeatVecDef rv C k → ∃ w <⁺ rv,
        ((∀ l, !lenDef l w → k = l) ∧ ∀ i < k, ∀ vi, !nthDef vi v i → ∀ v'i, !nthDef v'i w i → :⟪vi, v'i⟫:∈ C) ∧
        !qqFuncDef t k f v ∧ !β.func.graphDelta.pi y k f v w ⋯) )”
    (by simp))⟩

def graph : 𝚺₁.Semisentence (arity + 2) := .mkSigma
  “t y. ∃ pr <⁺ (t + y + 1)², !pairDef pr t y ∧ !β.blueprint.fixpointDef pr ⋯” (by simp)

def result : 𝚺₁.Semisentence (arity + 2) := .mkSigma
  “y t. (!pL.isUTermDef.pi t → !β.graph t y ⋯) ∧ (¬!pL.isUTermDef.sigma t → y = 0)” (by simp)

def resultVec : 𝚺₁.Semisentence (arity + 3) := .mkSigma
  “w' k w.
    (!pL.isUTermVecDef.pi k w → !lenDef k w' ∧ ∀ i < k, ∃ z, !nthDef z w i ∧ ∃ z', !nthDef z' w' i ∧ !β.graph.val z z' ⋯) ∧
    (¬!pL.isUTermVecDef.sigma k w → w' = 0)” (by simp)

end Blueprint

variable (V)

structure Construction (L : Arith.Language V) {k : ℕ} (φ : Blueprint pL k) where
  bvar : (Fin k → V) → V → V
  fvar : (Fin k → V) → V → V
  func : (Fin k → V) → V → V → V → V → V
  bvar_defined : 𝚺₁.DefinedFunction (fun v ↦ bvar (v ·.succ) (v 0)) φ.bvar
  fvar_defined : 𝚺₁.DefinedFunction (fun v ↦ fvar (v ·.succ) (v 0)) φ.fvar
  func_defined : 𝚺₁.DefinedFunction (fun v ↦ func (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.func

variable {V}

namespace Construction

variable {arity : ℕ} {β : Blueprint pL arity} (c : Construction V L β)

def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  L.IsUTerm (π₁ pr) ∧
  ( (∃ z, pr = ⟪^#z, c.bvar param z⟫) ∨
    (∃ x, pr = ⟪^&x, c.fvar param x⟫) ∨
    (∃ k f v w, (k = len w ∧ ∀ i < k, ⟪v.[i], w.[i]⟫ ∈ C) ∧ pr = ⟪^func k f v, c.func param k f v w⟫) )

lemma seq_bound {k s m : V} (Ss : Seq s) (hk : k = lh s) (hs : ∀ i z, ⟪i, z⟫ ∈ s → z < m) :
    s < exp ((k + m + 1)^2) := lt_exp_iff.mpr <| fun p hp ↦ by
  have : p < ⟪k, m⟫ := by
    simpa [hk] using
      pair_lt_pair (Ss.lt_lh_of_mem (show ⟪π₁ p, π₂ p⟫ ∈ s by simpa using hp)) (hs (π₁ p) (π₂ p) (by simpa using hp))
  exact lt_of_lt_of_le this (by simp)

private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
    ∃ t ≤ pr, ∃ y ≤ pr, pr = ⟪t, y⟫ ∧ L.IsUTerm t ∧
    ( (∃ z < t, t = ^#z ∧ y = c.bvar param z) ∨
      (∃ x < t, t = ^&x ∧ y = c.fvar param x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∃ w ≤ repeatVec C k,
        (k = len w ∧ ∀ i < k, ⟪v.[i], w.[i]⟫ ∈ C) ∧
        t = ^func k f v ∧ y = c.func param k f v w) ) := by
  constructor
  · rintro ⟨ht, H⟩
    refine ⟨π₁ pr, by simp, π₂ pr, by simp, by simp, ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, hk, rfl⟩)
    · left; exact ⟨z, by simp⟩
    · right; left; exact ⟨x, by simp⟩
    · right; right
      refine ⟨k, by simp, f, by simp, v, by simp, w, ?_, ⟨hk, hw⟩, by simp⟩
      · rcases hk; apply len_repeatVec_of_nth_le (fun i hi ↦ le_of_lt <| lt_of_mem_rng <| hw i hi)
  · rintro ⟨t, _, y, _, rfl, ht, H⟩
    refine ⟨by simpa using ht, ?_⟩
    rcases H with (⟨z, _, rfl, rfl⟩ | ⟨x, _, rfl, rfl⟩ | ⟨k, _, f, _, v, _, w, _, ⟨hk, hw⟩, rfl, rfl⟩)
    · left; exact ⟨z, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right
      exact ⟨k, f, v, w, ⟨hk, fun i hi ↦ hw i hi⟩, rfl⟩

/-- TODO: move-/
@[simp] lemma cons_app_9 {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 9 = s 8 := rfl

@[simp] lemma cons_app_10 {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 10 = s 9 := rfl

@[simp] lemma cons_app_11 {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 11 = s 10 := rfl

def construction : Fixpoint.Construction V β.blueprint where
  Φ := c.Phi
  defined :=
  ⟨by intro v
      /-
      simp? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint,
        eval_isUTermDef L, (isUTerm_defined L).proper.iff',
        c.bvar_defined.iff, c.bvar_defined.graph_delta.proper.iff',
        c.fvar_defined.iff, c.fvar_defined.graph_delta.proper.iff',
        c.func_defined.iff, c.func_defined.graph_delta.proper.iff']
      -/
      simp only [Nat.succ_eq_add_one, Blueprint.blueprint, Nat.reduceAdd, HierarchySymbol.Semiformula.val_sigma,
        Nat.add_zero, HierarchySymbol.Semiformula.sigma_mkDelta,
        HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
        Matrix.cons_val_one, Matrix.vecHead, LogicalConnective.HomClass.map_and,
        Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_two, Matrix.vecTail,
        Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.constant_eq_singleton, pair_defined_iff, Fin.isValue, Fin.succ_zero_eq_one,
        Matrix.cons_val_four, eval_isUTermDef L, LogicalConnective.HomClass.map_or,
        Semiformula.eval_bexLT, eval_qqBvarDef, Matrix.cons_app_five, c.bvar_defined.iff,
        LogicalConnective.Prop.and_eq, eval_qqFvarDef, c.fvar_defined.iff, Matrix.cons_val_three,
        Semiformula.eval_ex, Matrix.cons_app_seven, Matrix.cons_app_six, eval_repeatVec,
        eval_lenDef, Semiformula.eval_ballLT, eval_nthDef, Semiformula.eval_operator₃, cons_app_11,
        cons_app_10, cons_app_9, Matrix.cons_app_eight, eval_memRel, exists_eq_left, eval_qqFuncDef,
        Fin.succ_one_eq_two, c.func_defined.iff, LogicalConnective.Prop.or_eq,
        HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi, (isUTerm_defined L).proper.iff',
        c.bvar_defined.graph_delta.proper.iff', HierarchySymbol.Semiformula.graphDelta_val,
        c.fvar_defined.graph_delta.proper.iff', Semiformula.eval_all,
        LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂, Structure.Eq.eq,
        LogicalConnective.Prop.arrow_eq, forall_eq, c.func_defined.graph_delta.proper.iff']
      ,
    by  intro v
        /-
        simpa? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint, eval_isUTermDef L,
          c.bvar_defined.iff, c.fvar_defined.iff, c.func_defined.iff]
        using c.phi_iff _ _ _
        -/
        simpa only [Nat.succ_eq_add_one, Blueprint.blueprint,
          Nat.reduceAdd, HierarchySymbol.Semiformula.val_sigma,
          HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
          Semiformula.eval_bexLTSucc', Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          pair_defined_iff, Fin.isValue, Fin.succ_zero_eq_one, eval_isUTermDef L,
          LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT, eval_qqBvarDef,
          c.bvar_defined.iff, LogicalConnective.Prop.and_eq, eval_qqFvarDef, c.fvar_defined.iff,
          Matrix.cons_val_three, Semiformula.eval_ex, Matrix.cons_app_seven, Matrix.cons_app_six,
          Matrix.cons_app_five, Matrix.cons_val_four, eval_repeatVec, eval_lenDef,
          Semiformula.eval_ballLT, eval_nthDef, Semiformula.eval_operator₃, cons_app_11,
          cons_app_10, cons_app_9, Matrix.cons_app_eight, eval_memRel, exists_eq_left,
          eval_qqFuncDef, Fin.succ_one_eq_two, c.func_defined.iff,
          LogicalConnective.Prop.or_eq] using c.phi_iff _ _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC v pr ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)
    · left; exact ⟨z, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right; exact ⟨k, f, v, w, ⟨hk, fun i hi ↦ hC (hw i hi)⟩, rfl⟩

instance : c.construction.Finite where
  finite {C param pr h} := by
    rcases h with ⟨hp, (h | h | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)⟩
    · exact ⟨0, hp, Or.inl h⟩
    · exact ⟨0, hp, Or.inr <| Or.inl h⟩
    · exact ⟨⟪v, w⟫ + 1, hp, Or.inr <| Or.inr
        ⟨k, f, v, w,
          ⟨hk, fun i hi ↦ ⟨hw i hi, lt_succ_iff_le.mpr <| pair_le_pair (by simp) (by simp)⟩⟩, rfl⟩⟩

def Graph (param : Fin arity → V) (x y : V) : Prop := c.construction.Fixpoint param ⟪x, y⟫

variable {param : Fin arity → V} {n : V}

variable {c}

lemma Graph.case_iff {t y : V} :
    c.Graph param t y ↔
    L.IsUTerm t ∧
    ( (∃ z, t = ^#z ∧ y = c.bvar param z) ∨
      (∃ x, t = ^&x ∧ y = c.fvar param x) ∨
      (∃ k f v w, (k = len w ∧ ∀ i < k, c.Graph param v.[i] w.[i]) ∧
      t = ^func k f v ∧ y = c.func param k f v w) ) :=
  Iff.trans c.construction.case (by apply and_congr (by simp); simp; rfl)

variable (c)

lemma graph_defined : 𝚺₁.Defined (fun v ↦ c.Graph (v ·.succ.succ) (v 0) (v 1)) β.graph := by
  intro v
  simp [Blueprint.graph, c.construction.fixpoint_defined.iff]
  constructor
  · intro h; exact ⟨⟪v 0, v 1⟫, by simp, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v β.graph.val ↔ c.Graph (v ·.succ.succ) (v 0) (v 1) := (graph_defined c).df.iff v

instance graph_definable : 𝚺₁.Boldface (fun v ↦ c.Graph (v ·.succ.succ) (v 0) (v 1)) :=
  (graph_defined c).to_definable

instance graph_definable₂ (param) : 𝚺-[0 + 1]-Relation (c.Graph param) := by
  simpa using HierarchySymbol.Boldface.retractiont (n := 2) (graph_definable c) (#0 :> #1 :> fun i ↦ &(param i))

lemma graph_dom_isUTerm {t y} :
    c.Graph param t y → L.IsUTerm t := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_bvar_iff {z} :
    c.Graph param ^#z y ↔ y = c.bvar param z := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, rfl⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · simp at h; rcases h; rfl
    · simp [qqBvar, qqFvar] at h
    · simp [qqBvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, Or.inl ⟨z, by simp⟩⟩

lemma graph_fvar_iff (x) :
    c.Graph param ^&x y ↔ y = c.fvar param x := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · simp [qqFvar, qqBvar] at h
    · simp [qqFvar, qqFvar] at h; rcases h; rfl
    · simp [qqFvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, Or.inr <| Or.inl ⟨x, by simp⟩⟩

lemma graph_func {k f v w} (hkr : L.Func k f) (hv : L.IsUTermVec k v)
    (hkw : k = len w) (hw : ∀ i < k, c.Graph param v.[i] w.[i]) :
    c.Graph param (^func k f v) (c.func param k f v w) := by
  exact Graph.case_iff.mpr ⟨by simp [hkr, hv], Or.inr <| Or.inr ⟨k, f, v, w, ⟨hkw, hw⟩, by simp⟩⟩

lemma graph_func_inv {k f v y} :
    c.Graph param (^func k f v) y → ∃ w,
      (k = len w ∧ ∀ i < k, c.Graph param v.[i] w.[i]) ∧
      y = c.func param k f v w := by
  intro H
  rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨k, f, v, w, hw, h, rfl⟩)⟩
  · simp [qqFunc, qqBvar] at h
  · simp [qqFunc, qqFvar] at h
  · simp [qqFunc, qqFunc] at h; rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨w, hw, by rfl⟩

variable {c} (param n)

lemma graph_exists {t : V} : L.IsUTerm t → ∃ y, c.Graph param t y := by
  apply Language.IsUTerm.induction 𝚺 (P := fun t ↦ ∃ y, c.Graph param t y) (by definability)
  case hbvar =>
    intro z; exact ⟨c.bvar param z, by simp [c.graph_bvar_iff]⟩
  case hfvar =>
    intro x; exact ⟨c.fvar param x, by simp [c.graph_fvar_iff]⟩
  case hfunc =>
    intro k f v hkf hv ih
    have : ∃ w, len w = k ∧ ∀ i < k, c.Graph param v.[i] w.[i] := sigmaOne_skolem_vec (by definability) ih
    rcases this with ⟨w, hwk, hvw⟩
    exact ⟨c.func param k f v w, c.graph_func hkf hv (Eq.symm hwk) hvw⟩

lemma graph_unique {t y₁ y₂ : V} : c.Graph param t y₁ → c.Graph param t y₂ → y₁ = y₂ := by
  revert y₁ y₂
  suffices L.IsUTerm t → ∀ y₁ y₂, c.Graph param t y₁ → c.Graph param t y₂ → y₁ = y₂
  by intro u₁ u₂ h₁ h₂; exact this (c.graph_dom_isUTerm h₁) u₁ u₂ h₁ h₂
  intro ht
  apply Language.IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp [c.graph_bvar_iff]
  · intro x; simp [c.graph_fvar_iff]
  · intro k f v _ _ ih y₁ y₂ h₁ h₂
    rcases c.graph_func_inv h₁ with ⟨w₁, ⟨hk₁, hv₁⟩, rfl⟩
    rcases c.graph_func_inv h₂ with ⟨w₂, ⟨hk₂, hv₂⟩, rfl⟩
    have : w₁ = w₂ :=
      nth_ext (by simp [←hk₁, ←hk₂]) (fun i hi ↦
        ih i (by simpa [hk₁] using hi) _ _
          (hv₁ i (by simpa [hk₁] using hi)) (hv₂ i (by simpa [hk₁] using hi)))
    rw [this]

variable (c)

lemma graph_existsUnique {t : V} (ht : L.IsUTerm t) : ∃! y, c.Graph param t y := by
  rcases graph_exists param ht with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ graph_unique param h' hy)

lemma graph_existsUnique_total (t : V) : ∃! y,
    (L.IsUTerm t → c.Graph param t y) ∧ (¬L.IsUTerm t → y = 0) := by
  by_cases ht : L.IsUTerm t <;> simp [ht]; exact c.graph_existsUnique _ ht

def result (t : V) : V := Classical.choose! (c.graph_existsUnique_total param t)

def result_prop {t : V} (ht : L.IsUTerm t) : c.Graph param t (c.result param t) :=
  Classical.choose!_spec (c.graph_existsUnique_total param t) |>.1 ht

def result_prop_not {t : V} (ht : ¬L.IsUTerm t) : c.result param t = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_total param t) |>.2 ht

variable {c param}

lemma result_eq_of_graph {t y} (ht : L.IsUTerm t) (h : c.Graph param t y) :
    c.result param t = y := Eq.symm <| Classical.choose_uniq (c.graph_existsUnique_total param t) (by simp [h, ht])

@[simp] lemma result_bvar (z) : c.result param (^#z) = c.bvar param z :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_bvar_iff])

@[simp] lemma result_fvar (x) : c.result param (^&x) = c.fvar param x :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_fvar_iff])

lemma result_func {k f v w} (hkf : L.Func k f) (hv : L.IsUTermVec k v)
    (hkw : k = len w) (hw : ∀ i < k, c.result param v.[i] = w.[i]) :
    c.result param (^func k f v) = c.func param k f v w :=
  c.result_eq_of_graph (by simp [hkf, hv]) (c.graph_func hkf hv hkw (fun i hi ↦ by
    simpa [hw i hi] using c.result_prop param (hv.nth hi)))

section vec

lemma graph_existsUnique_vec {k w : V} (hw : L.IsUTermVec k w) :
    ∃! w' : V, k = len w' ∧ ∀ i < k, c.Graph param w.[i] w'.[i] := by
  have : ∀ i < k, ∃ y, c.Graph param w.[i] y := by
    intro i hi; exact ⟨c.result param w.[i], c.result_prop param (hw.nth hi)⟩
  rcases sigmaOne_skolem_vec (by definability) this
    with ⟨w', hw'k, hw'⟩
  refine ExistsUnique.intro w' ⟨hw'k.symm, hw'⟩ ?_
  intro w'' ⟨hkw'', hw''⟩
  refine nth_ext (by simp [hw'k, ←hkw'']) (by
    intro i hi;
    exact c.graph_unique param (hw'' i (by simpa [hkw''] using hi)) (hw' i (by simpa [hkw''] using hi)))

variable (c param)

lemma graph_existsUnique_vec_total (k w : V) : ∃! w',
    (L.IsUTermVec k w → k = len w' ∧ ∀ i < k, c.Graph param w.[i] w'.[i]) ∧
    (¬L.IsUTermVec k w → w' = 0) := by
  by_cases h : L.IsUTermVec k w <;> simp [h]; exact c.graph_existsUnique_vec h

def resultVec (k w : V) : V := Classical.choose! (c.graph_existsUnique_vec_total param k w)

@[simp] lemma resultVec_lh {k w : V} (hw : L.IsUTermVec k w) : len (c.resultVec param k w) = k :=
  Eq.symm <| Classical.choose!_spec (c.graph_existsUnique_vec_total param k w) |>.1 hw |>.1

lemma graph_of_mem_resultVec {k w : V} (hw : L.IsUTermVec k w) {i : V} (hi : i < k) :
    c.Graph param w.[i] (c.resultVec param k w).[i] :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total param k w) |>.1 hw |>.2 i hi

lemma nth_resultVec {k w i : V} (hw : L.IsUTermVec k w) (hi : i < k) :
    (c.resultVec param k w).[i] = c.result param w.[i] :=
  c.result_eq_of_graph (hw.nth hi) (c.graph_of_mem_resultVec param hw hi) |>.symm

@[simp] def resultVec_of_not {k w : V} (hw : ¬L.IsUTermVec k w) : c.resultVec param k w = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total param k w) |>.2 hw

@[simp] lemma resultVec_nil :
    c.resultVec param 0 0 = 0 := len_zero_iff_eq_nil.mp (by simp)

lemma resultVec_cons {k w t : V} (hw : L.IsUTermVec k w) (ht : L.IsUTerm t) :
    c.resultVec param (k + 1) (t ∷ w) = c.result param t ∷ c.resultVec param k w :=
  nth_ext (by simp [hw, hw.cons ht]) (by
    intro i hi
    have hi : i < k + 1 := by simpa [hw.cons ht, resultVec_lh] using hi
    rw [c.nth_resultVec param (hw.cons ht) hi]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [nth_resultVec]
    · simp [c.nth_resultVec param hw (by simpa using hi)])

end vec

variable (c)

@[simp] lemma result_func' {k f v} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    c.result param (^func k f v) = c.func param k f v (c.resultVec param k v) :=
  c.result_func hkf hv (by simp [hv]) (fun i hi ↦ c.nth_resultVec param hv hi |>.symm)

section

lemma result_defined : 𝚺₁.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.result := by
  intro v
  simp [Blueprint.result, HierarchySymbol.Semiformula.val_sigma, (isUTerm_defined L).proper.iff',
    eval_isUTermDef L, c.eval_graphDef, result, Classical.choose!_eq_iff]

@[simp] lemma result_graphDef (v) :
    Semiformula.Evalbm V v β.result.val ↔ v 0 = c.result (v ·.succ.succ) (v 1) := (result_defined c).df.iff v

private lemma resultVec_graph {w' k w} :
    w' = c.resultVec param k w ↔
    ( (L.IsUTermVec k w → k = len w' ∧ ∀ i < k, c.Graph param w.[i] w'.[i]) ∧
      (¬L.IsUTermVec k w → w' = 0) ) :=
  Classical.choose!_eq_iff (c.graph_existsUnique_vec_total param k w)

lemma resultVec_defined : 𝚺₁.DefinedFunction (fun v ↦ c.resultVec (v ·.succ.succ) (v 0) (v 1)) β.resultVec := by
  intro v
  simpa [Blueprint.resultVec, HierarchySymbol.Semiformula.val_sigma, L.isUTermVec_defined.proper.iff',
    eval_isUTermVecDef L, c.eval_graphDef] using c.resultVec_graph

lemma eval_resultVec (v : Fin (arity + 3) → V) :
    Semiformula.Evalbm V v β.resultVec.val ↔
    v 0 = c.resultVec (v ·.succ.succ.succ) (v 1) (v 2) := c.resultVec_defined.df.iff v

end

end Construction

end Language.TermRec

namespace IsUTerm.BV

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y z. y = z + 1” (by simp)
  fvar := .mkSigma “y x. y = 0” (by simp)
  func := .mkSigma “y k f v v'. !listMaxDef y v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ z)        := z + 1
  fvar (_ _)        := 0
  func (_ _ _ _ v') := listMax v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end IsUTerm.BV

section bv

open IsUTerm.BV

variable (L)

def Language.termBV (t : V) : V := (construction L).result ![] t

def Language.termBVVec (k v : V) : V := (construction L).resultVec ![] k v

variable {L}

@[simp] lemma Language.termBV_bvar (z) :
    L.termBV ^#z = z + 1 := by simp [Language.termBV, construction]

@[simp] lemma Language.termBV_fvar (x) :
    L.termBV ^&x = 0 := by simp [Language.termBV, construction]

@[simp] lemma Language.termBV_func {k f v} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    L.termBV (^func k f v) = listMax (L.termBVVec k v) := by
  simp [Language.termBV, construction, hkf, hv]; rfl

@[simp] lemma Language.len_termBVVec {v} (hv : L.IsUTermVec k v) :
    len (L.termBVVec k v) = k := (construction L).resultVec_lh _ hv

@[simp] lemma Language.nth_termBVVec {v} (hv : L.IsUTermVec k v) {i} (hi : i < k) :
    (L.termBVVec k v).[i] = L.termBV v.[i] := (construction L).nth_resultVec _ hv hi

@[simp] lemma Language.termBVVec_nil : L.termBVVec 0 0 = 0 := (construction L).resultVec_nil _

lemma Language.termBVVec_cons {k t ts : V} (ht : L.IsUTerm t) (hts : L.IsUTermVec k ts) :
    L.termBVVec (k + 1) (t ∷ ts) = L.termBV t ∷ L.termBVVec k ts :=
  (construction L).resultVec_cons ![] hts ht

section

variable (L)

def _root_.LO.FirstOrder.Arith.LDef.termBVDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termBVVecDef (pL : LDef) : 𝚺₁.Semisentence 3 := (blueprint pL).resultVec

lemma Language.termBV_defined : 𝚺₁-Function₁ L.termBV via pL.termBVDef := (construction L).result_defined

instance Language.termBV_definable : 𝚺₁-Function₁ L.termBV := L.termBV_defined.to_definable

instance Language.termBV_definable' : Γ-[k + 1]-Function₁ L.termBV := L.termBV_definable.of_sigmaOne

lemma Language.termBVVec_defined : 𝚺₁.DefinedFunction (fun v ↦ L.termBVVec (v 0) (v 1)) pL.termBVVecDef :=
  (construction L).resultVec_defined

instance Language.termBVVec_definable : 𝚺₁-Function₂ L.termBVVec := L.termBVVec_defined.to_definable

instance Language.termBVVec_definable' : Γ-[i + 1]-Function₂ L.termBVVec := L.termBVVec_definable.of_sigmaOne

end

end bv

section isSemiterm

variable (L)

def Language.IsSemiterm (n t : V) : Prop := L.IsUTerm t ∧ L.termBV t ≤ n

def Language.IsSemitermVec (k n v : V) : Prop := L.IsUTermVec k v ∧ ∀ i < k, L.termBV v.[i] ≤ n

abbrev Language.IsTerm (t : V) : Prop := L.IsSemiterm 0 t

abbrev Language.IsTermVec (k v : V) : Prop := L.IsSemitermVec k 0 v

variable {L}

lemma Language.IsSemiterm.isUTerm {n t : V} (h : L.IsSemiterm n t) : L.IsUTerm t := h.1

lemma Language.IsSemiterm.bv {n t : V} (h : L.IsSemiterm n t) : L.termBV t ≤ n := h.2

@[simp] lemma Language.IsSemitermVec.isUTerm {k n v : V} (h : L.IsSemitermVec k n v) : L.IsUTermVec k v := h.1

lemma Language.IsSemitermVec.bv {k n v : V} (h : L.IsSemitermVec k n v) {i} (hi : i < k) : L.termBV v.[i] ≤ n := h.2 i hi

lemma Language.IsSemitermVec.lh {k n v : V} (h : L.IsSemitermVec k n v) : len v = k := h.isUTerm.lh.symm

lemma Language.IsSemitermVec.nth {k n v : V} (h : L.IsSemitermVec k n v) {i} (hi : i < k) :
    L.IsSemiterm n v.[i] := ⟨h.isUTerm.nth hi, h.bv hi⟩

lemma Language.IsUTerm.isSemiterm {t : V} (h : L.IsUTerm t) : L.IsSemiterm (L.termBV t) t := ⟨h, by simp⟩

lemma Language.IsUTermVec.isSemitermVec {k v : V} (h : L.IsUTermVec k v) : L.IsSemitermVec k (listMax (L.termBVVec k v)) v :=
  ⟨h, fun i hi ↦ le_trans (by rw [Language.nth_termBVVec h hi]) (nth_le_listMax (i := i) (by simp [h, hi]))⟩

lemma Language.IsSemitermVec.iff {k n v : V} : L.IsSemitermVec k n v ↔ (len v = k ∧ ∀ i < k, L.IsSemiterm n v.[i]) := by
  constructor
  · intro h; exact ⟨h.lh, fun i hi ↦ h.nth hi⟩
  · intro ⟨hk, h⟩; exact ⟨⟨hk.symm, fun i hi ↦ h i hi |>.isUTerm⟩, fun i hi ↦ h i hi |>.bv⟩

@[simp] lemma Language.IsSemiterm.bvar {n z} :
    L.IsSemiterm n ^#z ↔ z < n := by simp [Language.IsSemiterm, succ_le_iff_lt]

@[simp] lemma Language.IsSemiterm.fvar (n x) :
    L.IsSemiterm n ^&x := by simp [Language.IsSemiterm]

@[simp] lemma Language.IsSemiterm.func {n k f v} :
    L.IsSemiterm n (^func k f v) ↔ L.Func k f ∧ L.IsSemitermVec k n v := by
  simp only [IsSemiterm, IsUTerm.func_iff]
  constructor
  · rintro ⟨⟨hf, hbv⟩, hv⟩
    exact ⟨hf, hbv, by
      intro i hi
      have : listMax (L.termBVVec k v) ≤ n := by simpa [termBV_func, hf, hbv] using hv
      simpa [hbv, hi] using listMaxss_le_iff.mp this i (by simp [hbv, hi])⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨hf, h.isUTerm⟩, by
      simp only [hf, h.isUTerm, termBV_func]
      apply listMaxss_le_iff.mpr
      intro i hi
      have hi : i < k := by simpa [hf, h.isUTerm] using hi
      simpa [hf, h.isUTerm, hi] using (h.nth hi).bv⟩

@[simp] lemma Language.IsSemitermVec.empty (n) : L.IsSemitermVec 0 n 0 := ⟨by simp, by simp⟩

@[simp] lemma Language.IsSemitermVec.empty_iff {n : V} : L.IsSemitermVec 0 n v ↔ v = 0 := by
  constructor
  · intro h; exact len_zero_iff_eq_nil.mp h.lh
  · rintro rfl; simp

@[simp] lemma Language.IsSemitermVec.cons_iff {n w t : V} :
    L.IsSemitermVec (k + 1) n (t ∷ w) ↔ L.IsSemiterm n t ∧ L.IsSemitermVec k n w := by
  constructor
  · intro h
    exact ⟨by simpa using h.nth (i := 0) (by simp),
      Language.IsSemitermVec.iff.mpr ⟨by simpa using h.lh, fun i hi ↦ by simpa using h.nth (show i + 1 < k + 1 by simp [hi])⟩⟩
  · rintro ⟨ht, hw⟩
    exact ⟨hw.isUTerm.cons ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simpa using hw.nth (by simpa using hi) |>.bv⟩

lemma Language.SemitermVec.cons {n m w t : V} (h : L.IsSemitermVec n m w) (ht : L.IsSemiterm m t) : L.IsSemitermVec (n + 1) m (t ∷ w) :=
  Language.IsSemitermVec.cons_iff.mpr ⟨ht, h⟩

@[simp] lemma Language.IsSemitermVec.singleton {n t : V} :
    L.IsSemitermVec 1 n ?[t] ↔ L.IsSemiterm n t := by
  rw [show (1 : V) = 0 + 1 by simp, Language.IsSemitermVec.cons_iff]; simp

@[simp] lemma Language.IsSemitermVec.doubleton {n t₁ t₂ : V} :
    L.IsSemitermVec 2 n ?[t₁, t₂] ↔ L.IsSemiterm n t₁ ∧ L.IsSemiterm n t₂ := by
  rw [show (2 : V) = 1 + 1 by simp [one_add_one_eq_two], Language.IsSemitermVec.cons_iff]; simp

section

variable (L)

def _root_.LO.FirstOrder.Arith.LDef.isSemitermDef (pL : LDef) : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !pL.isUTermDef.sigma p ∧ ∃ b, !pL.termBVDef b p ∧ b ≤ n” (by simp))
  (.mkPi “n p. !pL.isUTermDef.pi p ∧ ∀ b, !pL.termBVDef b p → b ≤ n” (by simp))

lemma Language.isSemiterm_defined : 𝚫₁-Relation L.IsSemiterm via pL.isSemitermDef where
  left := by
    intro v
    simp [Arith.LDef.isSemitermDef, HierarchySymbol.Semiformula.val_sigma,
      L.isUTerm_defined.df.iff, L.isUTerm_defined.proper.iff',
      L.termBV_defined.df.iff]
  right := by
    intro v
    simp [Arith.LDef.isSemitermDef, HierarchySymbol.Semiformula.val_sigma,
      L.isUTerm_defined.df.iff, L.termBV_defined.df.iff]; rfl

instance Language.isSemiterm_definable : 𝚫₁-Relation L.IsSemiterm := L.isSemiterm_defined.to_definable

instance Language.isSemiterm_defined' (Γ m) : Γ-[m + 1]-Relation L.IsSemiterm := L.isSemiterm_definable.of_deltaOne

def _root_.LO.FirstOrder.Arith.LDef.isSemitermVecDef (pL : LDef) : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “k n ps. !pL.isUTermVecDef.sigma k ps ∧ ∀ i < k, ∃ p, !nthDef p ps i ∧ ∃ b, !pL.termBVDef b p ∧ b ≤ n” (by simp))
  (.mkPi “k n ps. !pL.isUTermVecDef.pi k ps ∧ ∀ i < k, ∀ p, !nthDef p ps i → ∀ b, !pL.termBVDef b p → b ≤ n” (by simp))

lemma Language.isSemitermVec_defined : 𝚫₁-Relation₃ L.IsSemitermVec via pL.isSemitermVecDef where
  left := by
    intro v
    simp [Arith.LDef.isSemitermVecDef, HierarchySymbol.Semiformula.val_sigma,
      L.isUTermVec_defined.df.iff, L.isUTermVec_defined.proper.iff',
      L.termBV_defined.df.iff]
  right := by
    intro v
    simp [Arith.LDef.isSemitermVecDef, HierarchySymbol.Semiformula.val_sigma,
      L.isUTermVec_defined.df.iff, L.termBV_defined.df.iff]; rfl

instance Language.isSemitermVec_definable : 𝚫₁-Relation₃ L.IsSemitermVec := L.isSemitermVec_defined.to_definable

instance Language.isSemitermVec_defined' (Γ m) : Γ-[m + 1]-Relation₃ L.IsSemitermVec := L.isSemitermVec_definable.of_deltaOne

end

lemma Language.IsSemiterm.case_iff {n t : V} :
    L.IsSemiterm n t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.Func k f ∧ L.IsSemitermVec k n v ∧ t = ^func k f v) := by
  constructor
  · intro h
    rcases h.isUTerm.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, _, rfl⟩)
    · left; exact ⟨z, by simpa [succ_le_iff_lt] using h.bv, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right; exact ⟨k, f, v, hf, by simp_all, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · simp [hz]
    · simp
    · simp [hf, hv]

alias ⟨Language.IsSemiterm.case, Language.IsSemiterm.mk⟩ := Language.IsSemiterm.case_iff

lemma Language.IsSemiterm.induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.Func k f → L.IsSemitermVec k n v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, L.IsSemiterm n t → P t := by
  intro t ht
  suffices L.IsSemiterm n t → P t by exact this ht
  apply Language.IsUTerm.induction Γ ?_ ?_ ?_ ?_ t ht.isUTerm
  · definability
  · intro z; simp only [bvar]; exact hbvar z
  · intro x _; exact hfvar x
  · intro k f v hf _ ih h
    have hv : L.IsSemitermVec k n v := by simp_all
    exact hfunc k f v hf hv (fun i hi ↦ ih i hi (hv.nth hi))

@[simp] lemma Language.IsSemitermVec.nil (k : V): L.IsSemitermVec 0 k 0 := ⟨by simp, by simp⟩

@[simp] lemma Language.IsSemitermVec.cons {k n w t : V} (h : L.IsSemitermVec n k w) (ht : L.IsSemiterm k t) : L.IsSemitermVec (n + 1) k (t ∷ w) :=
  ⟨h.isUTerm.cons ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simp [h.bv (by simpa using hi)]⟩

end isSemiterm

end LO.Arith

end
