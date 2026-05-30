module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Language

@[expose] public section
namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

section term

noncomputable def qqBvar (z : V) : V := ⟪0, z⟫ + 1

noncomputable def qqFvar (x : V) : V := ⟪1, x⟫ + 1

noncomputable def qqFunc (k f v : V) : V := ⟪2, k, f, v⟫ + 1

def qqFuncN (k f v : ℕ) : ℕ := (Nat.pair 2 <| Nat.pair k <| Nat.pair f v) + 1

scoped prefix:max "^#" => qqBvar

scoped prefix:max "^&" => qqFvar

scoped prefix:max "^func " => qqFunc

lemma qqFuncN_eq_qqFunc (k f v : ℕ) : qqFuncN k f v = qqFunc k f v := by simp [qqFunc, qqFuncN, nat_pair_eq]

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

def _root_.LO.FirstOrder.Arithmetic.qqBvarDef : 𝚺₀.Semisentence 2 := .mkSigma “t z. ∃ t' < t, !pairDef t' 0 z ∧ t = t' + 1”

instance qqBvar_defined : 𝚺₀-Function₁ (qqBvar : V → V) via qqBvarDef := .mk fun _ ↦ by simp_all [qqBvarDef, qqBvar]

def _root_.LO.FirstOrder.Arithmetic.qqFvarDef : 𝚺₀.Semisentence 2 := .mkSigma “t x. ∃ t' < t, !pairDef t' 1 x ∧ t = t' + 1”

instance qqFvar_defined : 𝚺₀-Function₁ (qqFvar : V → V) via qqFvarDef := .mk fun v ↦ by simp_all [qqFvarDef, qqFvar]

private lemma qqFunc_graph {x k f v : V} :
    x = ^func k f v ↔ ∃ fv < x, fv = ⟪f, v⟫ ∧ ∃ kfv < x, kfv = ⟪k, fv⟫ ∧ ∃ x' < x, x' = ⟪2, kfv⟫ ∧ x = x' + 1 :=
  ⟨by rintro rfl
      exact ⟨⟪f, v⟫, lt_succ_iff_le.mpr <| le_trans (le_pair_right _ _) (le_pair_right _ _), rfl,
        ⟪k, f, v⟫, lt_succ_iff_le.mpr <| by simp, rfl,
        ⟪2, k, f, v⟫, by simp [qqFunc], rfl, rfl⟩,
   by rintro ⟨_, _, rfl, _, _, rfl, _, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arithmetic.qqFuncDef : 𝚺₀.Semisentence 4 := .mkSigma
  “x k f v. ∃ fv < x, !pairDef fv f v ∧ ∃ kfv < x, !pairDef kfv k fv ∧ ∃ x' < x, !pairDef x' 2 kfv ∧ x = x' + 1”

instance qqFunc_defined : 𝚺₀-Function₃ (qqFunc : V → V → V → V) via qqFuncDef := .mk fun v ↦ by simp [qqFuncDef, qqFunc_graph]

namespace FormalizedTerm

variable (L)

def Phi (C : Set V) (t : V) : Prop :=
  (∃ z, t = ^#z) ∨ (∃ x, t = ^&x) ∨ (∃ k f v : V, L.IsFunc k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v)

private lemma phi_iff (C : V) (t : V) :
    Phi L {x | x ∈ C} t ↔
    (∃ z < t, t = ^#z) ∨
    (∃ x < t, t = ^&x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t, L.IsFunc k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v) where
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

def blueprint : Fixpoint.Blueprint 0 where
  core := .mkDelta
    (.mkSigma “t C.
      (∃ z < t, !qqBvarDef t z) ∨
      (∃ x < t, !qqFvarDef t x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, !L.isFunc k f ∧ !lenDef k v ∧ (∀ i < k, ∃ u, !nthDef u v i ∧ u ∈ C) ∧ !qqFuncDef t k f v)”
    (by simp))
    (.mkPi “t C.
      (∃ z < t, !qqBvarDef t z) ∨
      (∃ x < t, !qqFvarDef t x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, !L.isFunc k f ∧ (∀ l, !lenDef l v → k = l) ∧ (∀ i < k, ∀ u, !nthDef u v i → u ∈ C) ∧ !qqFuncDef t k f v)”
    (by simp))

def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := ⟨by intro v; simp [blueprint], by intro v; simp [blueprint, phi_iff]⟩
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

def IsUTerm : V → Prop := (construction L).Fixpoint ![]

/-- Note: `noncomputable` attribute to prohibit compilation of a large term. This is necessary for Zoo and integration with Verso. -/
noncomputable def isUTerm : 𝚫₁.Semisentence 1 := (blueprint L).fixpointDefΔ₁

variable {L}

namespace IsUTerm

instance defined : 𝚫₁-Predicate (IsUTerm L (V := V)) via (isUTerm L) := (construction L).fixpoint_definedΔ₁

instance definable : 𝚫₁-Predicate (IsUTerm L (V := V)) := defined.to_definable

instance definable' (Γ) : Γ-[m + 1]-Predicate (IsUTerm L (V := V)) := definable.of_deltaOne

end IsUTerm

variable (L)

def IsUTermVec (n w : V) : Prop := n = len w ∧ ∀ i < n, IsUTerm L w.[i]

noncomputable def isUTermVec : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n w. !lenDef n w ∧ ∀ i < n, ∃ u, !nthDef u w i ∧ !(isUTerm L).sigma u”)
  (.mkPi “n w. (∀ l, !lenDef l w → n = l) ∧ ∀ i < n, ∀ u, !nthDef u w i → !(isUTerm L).pi u”)

variable {L}

namespace IsUTermVec

protected lemma lh {n w : V} (h : IsUTermVec L n w) : n = len w := h.1

lemma nth {n w : V} (h : IsUTermVec L n w) {i} : i < n → IsUTerm L w.[i] := h.2 i

@[simp] lemma empty : IsUTermVec (V := V) L 0 0 := ⟨by simp, by simp⟩

@[simp] lemma empty_iff : IsUTermVec L 0 v ↔ v = 0 := by
  constructor
  · intro h; exact len_zero_iff_eq_nil.mp h.lh.symm
  · rintro rfl; simp

lemma two_iff {v : V} : IsUTermVec L 2 v ↔ ∃ t₁ t₂, IsUTerm L t₁ ∧ IsUTerm L t₂ ∧ v = ?[t₁, t₂] := by
  constructor
  · intro h
    rcases eq_doubleton_of_len_eq_two.mp h.lh.symm with ⟨t₁, t₂, rfl⟩
    exact ⟨t₁, t₂, by simpa using h.nth (show 0 < 2 by simp), by simpa using h.nth (show 1 < 2 by simp), rfl⟩
  · rintro ⟨t₁, t₂, h₁, h₂, rfl⟩; exact ⟨by simp [one_add_one_eq_two], by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h₁, h₂]⟩

@[simp] lemma adjoin {n w t : V} (h : IsUTermVec L n w) (ht : IsUTerm L t) : IsUTermVec L (n + 1) (t ∷ w) :=
  ⟨by simp [h.lh], fun i hi ↦ by
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simpa
    · simpa using h.nth (by simpa using hi)⟩

@[simp] lemma adjoin₁_iff {t : V} :
    IsUTermVec L 1 (?[t] : V) ↔ IsUTerm L t := by
  constructor
  · intro h; simpa using h.nth (i := 0) (by simp)
  · intro h; simpa using empty.adjoin h

@[simp] lemma mkSeq₂_iff {t₁ t₂ : V} :
    IsUTermVec L 2 (?[t₁, t₂] : V) ↔ IsUTerm L t₁ ∧ IsUTerm L t₂ := by
  constructor
  · intro h; exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨h₁, h₂⟩
    simpa [one_add_one_eq_two] using (adjoin₁_iff.mpr h₂).adjoin h₁

section

instance defined : 𝚫₁-Relation (IsUTermVec (V := V) L) via (isUTermVec L) :=
  ⟨by intro v; simp [isUTermVec, HierarchySymbol.Semiformula.val_sigma, IsUTerm.defined.proper.iff'],
   by intro v; simp [isUTermVec, HierarchySymbol.Semiformula.val_sigma, IsUTermVec]⟩

instance definable : 𝚫₁-Relation (IsUTermVec (V := V) L) := defined.to_definable

instance definable' (Γ) : Γ-[m + 1]-Relation (IsUTermVec (V := V) L) := definable.of_deltaOne

end

end IsUTermVec

namespace IsUTerm

lemma case_iff {t : V} :
    IsUTerm L t ↔
    (∃ z, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.IsFunc k f ∧ IsUTermVec L k v ∧ t = ^func k f v) := by
  simpa [construction, Phi, IsUTermVec, and_assoc] using (construction L).case

alias ⟨case, mk⟩ := case_iff

@[simp] lemma bvar {z : V} : IsUTerm L ^#z :=
  mk (Or.inl ⟨z, rfl⟩)

@[simp] lemma fvar (x : V) : IsUTerm L ^&x :=
  mk (Or.inr <| Or.inl ⟨x, rfl⟩)

@[simp] lemma func_iff {k f v : V} :
    IsUTerm L (^func k f v) ↔ L.IsFunc k f ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨_, h⟩ | ⟨x, h⟩ | ⟨k', f', w, hkf, ⟨hk, hv⟩, h⟩)
      · simp [qqFunc, qqBvar] at h
      · simp [qqFunc, qqFvar] at h
      · rcases (show k = k' ∧ f = f' ∧ v = w by simpa [qqFunc] using h) with ⟨rfl, rfl, rfl⟩
        exact ⟨hkf, hk, hv⟩,
   by rintro ⟨hkf, hk, hv⟩; exact mk <| Or.inr <| Or.inr ⟨k, f, v, hkf, ⟨hk, hv⟩, rfl⟩⟩

lemma func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    IsUTerm L (^func k f v) := func_iff.mpr ⟨hkf, hv⟩

lemma induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hbvar : ∀ z, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.IsFunc k f → IsUTermVec L k v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, IsUTerm L t → P t :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · exact hbvar z
    · exact hfvar x
    · exact hfunc k f v hkf ⟨hk, fun i hi ↦ hC _ (h i hi) |>.1⟩ (fun i hi ↦ hC _ (h i hi) |>.2))

end IsUTerm

end term

namespace Language.TermRec

structure Blueprint (arity : ℕ) where
  bvar : 𝚺₁.Semisentence (arity + 2)
  fvar : 𝚺₁.Semisentence (arity + 2)
  func : 𝚺₁.Semisentence (arity + 5)

namespace Blueprint

variable (L) (β : Blueprint arity)

noncomputable def blueprint : Fixpoint.Blueprint arity := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ t <⁺ pr, ∃ y <⁺ pr, !pairDef pr t y ∧ !(isUTerm L).sigma t ∧
    ( (∃ z < t, !qqBvarDef t z ∧ !β.bvar y z ⋯) ∨
      (∃ x < t, !qqFvarDef t x ∧ !β.fvar y x ⋯) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∃ rv, !repeatVecDef rv C k ∧ ∃ w <⁺ rv,
        (!lenDef k w ∧ ∀ i < k, ∃ vi, !nthDef vi v i ∧ ∃ v'i, !nthDef v'i w i ∧ :⟪vi, v'i⟫:∈ C) ∧
        !qqFuncDef t k f v ∧ !β.func y k f v w ⋯) )”)
  (.mkPi “pr C.
    ∃ t <⁺ pr, ∃ y <⁺ pr, !pairDef pr t y ∧ !(isUTerm L).pi t ∧
    ( (∃ z < t, !qqBvarDef t z ∧ !β.bvar.graphDelta.pi y z ⋯) ∨
      (∃ x < t, !qqFvarDef t x ∧ !β.fvar.graphDelta.pi y x ⋯) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∀ rv, !repeatVecDef rv C k → ∃ w <⁺ rv,
        ((∀ l, !lenDef l w → k = l) ∧ ∀ i < k, ∀ vi, !nthDef vi v i → ∀ v'i, !nthDef v'i w i → :⟪vi, v'i⟫:∈ C) ∧
        !qqFuncDef t k f v ∧ !β.func.graphDelta.pi y k f v w ⋯) )”)⟩

noncomputable def graph : 𝚺₁.Semisentence (arity + 2) := .mkSigma
  “t y. ∃ pr <⁺ (t + y + 1)², !pairDef pr t y ∧ !(β.blueprint L).fixpointDef pr ⋯”

noncomputable def result : 𝚺₁.Semisentence (arity + 2) := .mkSigma
  “y t. (!(isUTerm L).pi t → !(β.graph L) t y ⋯) ∧ (¬!(isUTerm L).sigma t → y = 0)”

noncomputable def resultVec : 𝚺₁.Semisentence (arity + 3) := .mkSigma
  “w' k w.
    (!(isUTermVec L).pi k w → !lenDef k w' ∧ ∀ i < k, ∃ z, !nthDef z w i ∧ ∃ z', !nthDef z' w' i ∧ !(β.graph L).val z z' ⋯) ∧
    (¬!(isUTermVec L).sigma k w → w' = 0)”

end Blueprint

variable (L V)

structure Construction {k : ℕ} (φ : Blueprint k) where
  bvar : (Fin k → V) → V → V
  fvar : (Fin k → V) → V → V
  func : (Fin k → V) → V → V → V → V → V
  bvar_defined : 𝚺₁.DefinedFunction (fun v ↦ bvar (v ·.succ) (v 0)) φ.bvar
  fvar_defined : 𝚺₁.DefinedFunction (fun v ↦ fvar (v ·.succ) (v 0)) φ.fvar
  func_defined : 𝚺₁.DefinedFunction (fun v ↦ func (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.func

variable {V}

namespace Construction

variable {arity : ℕ} {β : Blueprint arity} (c : Construction V β)

def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  IsUTerm L (π₁ pr) ∧
  ( (∃ z, pr = ⟪^#z, c.bvar param z⟫) ∨
    (∃ x, pr = ⟪^&x, c.fvar param x⟫) ∨
    (∃ k f v w, (k = len w ∧ ∀ i < k, ⟪v.[i], w.[i]⟫ ∈ C) ∧ pr = ⟪^func k f v, c.func param k f v w⟫) )

lemma seq_bound {k s m : V} (Ss : Seq s) (hk : k = lh s) (hs : ∀ i z, ⟪i, z⟫ ∈ s → z < m) :
    s < Exp.exp ((k + m + 1)^2) := lt_exp_iff.mpr <| fun p hp ↦ by
  have : p < ⟪k, m⟫ := by
    simpa [hk] using
      pair_lt_pair (Ss.lt_lh_of_mem (show ⟪π₁ p, π₂ p⟫ ∈ s by simpa using hp)) (hs (π₁ p) (π₂ p) (by simpa using hp))
  exact lt_of_lt_of_le this (by simp)

private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi L param {x | x ∈ C} pr ↔
    ∃ t ≤ pr, ∃ y ≤ pr, pr = ⟪t, y⟫ ∧ IsUTerm L t ∧
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

def construction : Fixpoint.Construction V (β.blueprint L) where
  Φ := c.Phi L
  defined := .mk <| by
    constructor
    · intro v
      simp [Blueprint.blueprint,
        c.bvar_defined.iff, c.bvar_defined.graph_delta.iff_delta_pi,
        c.fvar_defined.iff, c.fvar_defined.graph_delta.iff_delta_pi,
        c.func_defined.iff, c.func_defined.graph_delta.iff_delta_pi]
    · intro v
      symm
      simpa [Blueprint.blueprint, c.bvar_defined.iff, c.fvar_defined.iff, c.func_defined.iff]
        using c.phi_iff L _ _ _
  monotone := by
    unfold Phi
    rintro C C' hC v pr ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)
    · left; exact ⟨z, rfl⟩
    · right; left; exact ⟨x, rfl⟩
    · right; right; exact ⟨k, f, v, w, ⟨hk, fun i hi ↦ hC (hw i hi)⟩, rfl⟩

instance : (c.construction L).Finite where
  finite {C param pr h} := by
    rcases h with ⟨hp, (h | h | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)⟩
    · exact ⟨0, hp, Or.inl h⟩
    · exact ⟨0, hp, Or.inr <| Or.inl h⟩
    · exact ⟨⟪v, w⟫ + 1, hp, Or.inr <| Or.inr
        ⟨k, f, v, w,
          ⟨hk, fun i hi ↦ ⟨hw i hi, lt_succ_iff_le.mpr <| pair_le_pair (by simp) (by simp)⟩⟩, rfl⟩⟩

def Graph (param : Fin arity → V) (x y : V) : Prop := (c.construction L).Fixpoint param ⟪x, y⟫

variable {param : Fin arity → V} {n : V}

variable {L c}

lemma Graph.case_iff {t y : V} :
    c.Graph L param t y ↔
    IsUTerm L t ∧
    ( (∃ z, t = ^#z ∧ y = c.bvar param z) ∨
      (∃ x, t = ^&x ∧ y = c.fvar param x) ∨
      (∃ k f v w, (k = len w ∧ ∀ i < k, c.Graph L param v.[i] w.[i]) ∧
      t = ^func k f v ∧ y = c.func param k f v w) ) :=
  Iff.trans (c.construction L).case (by apply and_congr (by simp); simp; rfl)

variable (c)

lemma graph_defined : 𝚺₁.Defined (fun v ↦ c.Graph L (v ·.succ.succ) (v 0) (v 1)) (β.graph L) := .mk fun v ↦ by
  simp [Blueprint.graph, (c.construction L).fixpoint_defined.iff, Graph]

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v (β.graph L).val ↔ c.Graph L (v ·.succ.succ) (v 0) (v 1) := (graph_defined c).iff

instance graph_definable : 𝚺₁.Definable fun v ↦ c.Graph L (v ·.succ.succ) (v 0) (v 1) :=
  (graph_defined c).to_definable

instance graph_definable₂ (param) : 𝚺-[0 + 1]-Relation (c.Graph L param) := by
  simpa using HierarchySymbol.Definable.retractiont (n := 2) (graph_definable c) (#0 :> #1 :> fun i ↦ &(param i))

lemma graph_dom_isUTerm {t y} :
    c.Graph L param t y → IsUTerm L t := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_bvar_iff {z} :
    c.Graph L param ^#z y ↔ y = c.bvar param z := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, rfl⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · rcases (by simpa using h); rfl
    · simp [qqBvar, qqFvar] at h
    · simp [qqBvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, Or.inl ⟨z, by simp⟩⟩

lemma graph_fvar_iff (x) :
    c.Graph L param ^&x y ↔ y = c.fvar param x := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · simp [qqFvar, qqBvar] at h
    · rcases (by simpa using h); rfl
    · simp [qqFvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, Or.inr <| Or.inl ⟨x, by simp⟩⟩

lemma graph_func {k f v w} (hkr : L.IsFunc k f) (hv : IsUTermVec L k v)
    (hkw : k = len w) (hw : ∀ i < k, c.Graph L param v.[i] w.[i]) :
    c.Graph L param (^func k f v) (c.func param k f v w) := by
  exact Graph.case_iff.mpr ⟨by simp [hkr, hv], Or.inr <| Or.inr ⟨k, f, v, w, ⟨hkw, hw⟩, by simp⟩⟩

lemma graph_func_inv {k f v y} :
    c.Graph L param (^func k f v) y → ∃ w,
      (k = len w ∧ ∀ i < k, c.Graph L param v.[i] w.[i]) ∧
      y = c.func param k f v w := by
  intro H
  rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨k', f', v', w, hw, h, rfl⟩)⟩
  · simp [qqFunc, qqBvar] at h
  · simp [qqFunc, qqFvar] at h
  · rcases show k = k' ∧ f = f' ∧ v = v' by simpa [qqFunc, qqFunc] using h with ⟨rfl, rfl, rfl⟩
    exact ⟨w, hw, by rfl⟩

variable {c} (param n)

lemma graph_exists {t : V} : IsUTerm L t → ∃ y, c.Graph L param t y := by
  apply IsUTerm.induction 𝚺 (P := fun t ↦ ∃ y, c.Graph L param t y) (by definability)
  case hbvar =>
    intro z; exact ⟨c.bvar param z, by simp [c.graph_bvar_iff]⟩
  case hfvar =>
    intro x; exact ⟨c.fvar param x, by simp [c.graph_fvar_iff]⟩
  case hfunc =>
    intro k f v hkf hv ih
    have : ∃ w, len w = k ∧ ∀ i < k, c.Graph L param v.[i] w.[i] := sigmaOne_skolem_vec (by definability) ih
    rcases this with ⟨w, hwk, hvw⟩
    exact ⟨c.func param k f v w, c.graph_func hkf hv (Eq.symm hwk) hvw⟩

lemma graph_unique {t y₁ y₂ : V} : c.Graph L param t y₁ → c.Graph L param t y₂ → y₁ = y₂ := by
  revert y₁ y₂
  suffices IsUTerm L t → ∀ y₁ y₂, c.Graph L param t y₁ → c.Graph L param t y₂ → y₁ = y₂
  by intro u₁ u₂ h₁ h₂; exact this (c.graph_dom_isUTerm h₁) u₁ u₂ h₁ h₂
  intro ht
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
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

variable (L c)

lemma graph_existsUnique {t : V} (ht : IsUTerm L t) : ∃! y, c.Graph L param t y := by
  rcases graph_exists param ht with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ graph_unique param h' hy)

lemma graph_existsUnique_total (t : V) : ∃! y,
    (IsUTerm L t → c.Graph L param t y) ∧ (¬IsUTerm L t → y = 0) := by
  by_cases ht : IsUTerm L t <;> simp [ht, c.graph_existsUnique L param]

noncomputable def result (t : V) : V := Classical.choose! (c.graph_existsUnique_total L param t)

def result_prop {t : V} (ht : IsUTerm L t) : c.Graph L param t (c.result L param t) :=
  Classical.choose!_spec (c.graph_existsUnique_total L param t) |>.1 ht

def result_prop_not {t : V} (ht : ¬IsUTerm L t) : c.result L param t = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_total L param t) |>.2 ht

variable {L c param}

lemma result_eq_of_graph {t y} (ht : IsUTerm L t) (h : c.Graph L param t y) :
    c.result L param t = y := Eq.symm <| Classical.choose_uniq (c.graph_existsUnique_total L param t) (by simp [h, ht])

@[simp] lemma result_bvar (z) : c.result L param (^#z) = c.bvar param z :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_bvar_iff])

@[simp] lemma result_fvar (x) : c.result L param (^&x) = c.fvar param x :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_fvar_iff])

lemma result_func {k f v w} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v)
    (hkw : k = len w) (hw : ∀ i < k, c.result L param v.[i] = w.[i]) :
    c.result L param (^func k f v) = c.func param k f v w :=
  c.result_eq_of_graph (by simp [hkf, hv]) (c.graph_func hkf hv hkw (fun i hi ↦ by
    simpa [hw i hi] using c.result_prop L param (hv.nth hi)))

section vec

lemma graph_existsUnique_vec {k w : V} (hw : IsUTermVec L k w) :
    ∃! w' : V, k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i] := by
  have : ∀ i < k, ∃ y, c.Graph L param w.[i] y := by
    intro i hi; exact ⟨c.result L param w.[i], c.result_prop L param (hw.nth hi)⟩
  rcases sigmaOne_skolem_vec (by definability) this
    with ⟨w', hw'k, hw'⟩
  refine ExistsUnique.intro w' ⟨hw'k.symm, hw'⟩ ?_
  intro w'' ⟨hkw'', hw''⟩
  refine nth_ext (by simp [hw'k, ←hkw'']) (by
    intro i hi;
    exact c.graph_unique param (hw'' i (by simpa [hkw''] using hi)) (hw' i (by simpa [hkw''] using hi)))

variable (L c param)

lemma graph_existsUnique_vec_total (k w : V) : ∃! w',
    (IsUTermVec L k w → k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i]) ∧
    (¬IsUTermVec L k w → w' = 0) := by
  by_cases h : IsUTermVec L k w <;> simp [h, c.graph_existsUnique_vec]

noncomputable def resultVec (k w : V) : V := Classical.choose! (c.graph_existsUnique_vec_total L param k w)

@[simp] lemma resultVec_lh {k w : V} (hw : IsUTermVec L k w) : len (c.resultVec L param k w) = k :=
  Eq.symm <| Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.1 hw |>.1

lemma graph_of_mem_resultVec {k w : V} (hw : IsUTermVec L k w) {i : V} (hi : i < k) :
    c.Graph L param w.[i] (c.resultVec L param k w).[i] :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.1 hw |>.2 i hi

lemma nth_resultVec {k w i : V} (hw : IsUTermVec L k w) (hi : i < k) :
    (c.resultVec L param k w).[i] = c.result L param w.[i] :=
  c.result_eq_of_graph (hw.nth hi) (c.graph_of_mem_resultVec L param hw hi) |>.symm

@[simp] def resultVec_of_not {k w : V} (hw : ¬IsUTermVec L k w) : c.resultVec L param k w = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.2 hw

@[simp] lemma resultVec_nil :
    c.resultVec L param 0 0 = 0 := len_zero_iff_eq_nil.mp (by simp)

lemma resultVec_cons {k w t : V} (hw : IsUTermVec L k w) (ht : IsUTerm L t) :
    c.resultVec L param (k + 1) (t ∷ w) = c.result L param t ∷ c.resultVec L param k w :=
  nth_ext (by simp [hw, hw.adjoin ht]) (by
    intro i hi
    have hi : i < k + 1 := by simpa [hw.adjoin ht, resultVec_lh] using hi
    rw [c.nth_resultVec L param (hw.adjoin ht) hi]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [c.nth_resultVec L param hw (by simpa using hi)])

end vec

variable (c)

@[simp] lemma result_func' {k f v} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    c.result L param (^func k f v) = c.func param k f v (c.resultVec L param k v) :=
  c.result_func hkf hv (by simp [hv]) (fun i hi ↦ c.nth_resultVec L param hv hi |>.symm)

section

lemma result_defined : 𝚺₁.DefinedFunction (fun v ↦ c.result L (v ·.succ) (v 0)) (β.result L) := .mk fun v ↦ by
  simp [Blueprint.result, HierarchySymbol.Semiformula.val_sigma, IsUTerm.defined.proper.iff',
    c.eval_graphDef, result, Classical.choose!_eq_iff_right]

@[simp] lemma result_graphDef (v) :
    Semiformula.Evalbm V v (β.result L).val ↔ v 0 = c.result L (v ·.succ.succ) (v 1) := (result_defined c).iff

private lemma resultVec_graph {w' k w} :
    w' = c.resultVec L param k w ↔
    ( (IsUTermVec L k w → k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i]) ∧
      (¬IsUTermVec L k w → w' = 0) ) :=
  Classical.choose!_eq_iff_right (c.graph_existsUnique_vec_total L param k w)

lemma resultVec_defined : 𝚺₁.DefinedFunction (fun v ↦ c.resultVec L (v ·.succ.succ) (v 0) (v 1)) (β.resultVec L) := .mk fun v ↦ by
  symm
  simpa [Blueprint.resultVec, HierarchySymbol.Semiformula.val_sigma, IsUTermVec.defined.proper.iff',
    c.eval_graphDef] using c.resultVec_graph

lemma eval_resultVec (v : Fin (arity + 3) → V) :
    Semiformula.Evalbm V v (β.resultVec L).val ↔
    v 0 = c.resultVec L (v ·.succ.succ.succ) (v 1) (v 2) := c.resultVec_defined.iff

end

end Construction

end Language.TermRec

namespace IsUTerm.BV

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = z + 1”
  fvar := .mkSigma “y x. y = 0”
  func := .mkSigma “y k f v v'. !listMaxDef y v'”

variable (L)

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := z + 1
  fvar (_ _)        := 0
  func (_ _ _ _ v') := listMax v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end IsUTerm.BV

section bv

open IsUTerm.BV

variable (L)

noncomputable def termBV (t : V) : V := construction.result L ![] t

noncomputable def termBVVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def termBVGraph : 𝚺₁.Semisentence 2 := blueprint.result L

noncomputable def termBVVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp] lemma termBV_bvar (z : V) :
    termBV L ^#z = z + 1 := by simp [termBV, construction]

@[simp] lemma termBV_fvar (x : V) :
    termBV L ^&x = 0 := by simp [termBV, construction]

@[simp] lemma termBV_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termBV L (^func k f v) = listMax (termBVVec L k v) := by
  simp [termBV, construction, hkf, hv]; rfl

@[simp] lemma len_termBVVec {v : V} (hv : IsUTermVec L k v) :
    len (termBVVec L k v) = k := construction.resultVec_lh L _ hv

@[simp] lemma nth_termBVVec {v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) :
    (termBVVec L k v).[i] = termBV L v.[i] := construction.nth_resultVec L _ hv hi

@[simp] lemma termBVVec_nil : termBVVec L 0 0 = 0 := construction.resultVec_nil L _

lemma termBVVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termBVVec L (k + 1) (t ∷ ts) = termBV L t ∷ termBVVec L k ts :=
  construction.resultVec_cons L ![] hts ht

section

instance termBV.defined : 𝚺₁-Function₁ (termBV (V := V) L) via (termBVGraph L) := construction.result_defined

instance termBV.definable : 𝚺₁-Function₁ (termBV (V := V) L) := termBV.defined.to_definable

instance termBV.definable' : Γ-[k + 1]-Function₁ (termBV (V := V) L) := termBV.definable.of_sigmaOne

instance termBVVec.defined : 𝚺₁-Function₂ (termBVVec (V := V) L) via (termBVVecGraph L) :=
  construction.resultVec_defined

instance termBVVec.definable : 𝚺₁-Function₂ (termBVVec (V := V) L) := termBVVec.defined.to_definable

instance termBVVec.definable' : Γ-[i + 1]-Function₂ (termBVVec (V := V) L) := termBVVec.definable.of_sigmaOne

end

end bv

section isSemiterm

variable (L)

class IsSemiterm (n t : V) : Prop where
  isUTerm : IsUTerm L t
  bv : termBV L t ≤ n

class IsSemitermVec (k n v : V) : Prop where
  isUTermVec : IsUTermVec L k v
  bv : ∀  {i}, i < k → termBV L v.[i] ≤ n

noncomputable def isSemiterm : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !(isUTerm L).sigma p ∧ ∃ b, !(termBVGraph L) b p ∧ b ≤ n”)
  (.mkPi “n p. !(isUTerm L).pi p ∧ ∀ b, !(termBVGraph L) b p → b ≤ n”)

noncomputable def isSemitermVec : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “k n ps. !(isUTermVec L).sigma k ps ∧ ∀ i < k, ∃ p, !nthDef p ps i ∧ ∃ b, !(termBVGraph L) b p ∧ b ≤ n”)
  (.mkPi “k n ps. !(isUTermVec L).pi k ps ∧ ∀ i < k, ∀ p, !nthDef p ps i → ∀ b, !(termBVGraph L) b p → b ≤ n”)

abbrev IsTerm (t : V) : Prop := IsSemiterm L 0 t

abbrev IsTermVec (k v : V) : Prop := IsSemitermVec L k 0 v

variable {L}

lemma IsSemiterm.def {n} {t : V} : IsSemiterm L n t ↔ IsUTerm L t ∧ termBV L t ≤ n :=
  ⟨by rintro ⟨h, bv⟩; exact ⟨h, bv⟩, by rintro ⟨h, bv⟩; exact ⟨h, bv⟩⟩

lemma IsSemitermVec.def {n} {v : V} : IsSemitermVec L k n v ↔ IsUTermVec L k v ∧ ∀ i < k, termBV (V := V) L v.[i] ≤ n :=
  ⟨by rintro ⟨h, bv⟩; exact ⟨h, fun _ ↦ bv⟩, by rintro ⟨h, bv⟩; exact ⟨h, bv _⟩⟩

@[simp] lemma IsSemitermVec.isUTerm {k n v : V} (h : IsSemitermVec L k n v) : IsUTermVec L k v := h.1

lemma IsSemitermVec.lh {k n v : V} (h : IsSemitermVec L k n v) : len v = k := h.isUTerm.lh.symm

lemma IsSemitermVec.nth {k n v : V} (h : IsSemitermVec L k n v) {i} (hi : i < k) :
    IsSemiterm L n v.[i] := ⟨h.isUTerm.nth hi, h.bv hi⟩

lemma IsUTerm.isSemiterm {t : V} (h : IsUTerm L t) : IsSemiterm L (termBV L t) t := ⟨h, by simp⟩

lemma IsUTermVec.isSemitermVec {k v : V} (h : IsUTermVec L k v) : IsSemitermVec L k (listMax (termBVVec L k v)) v :=
  ⟨h, fun {i} hi ↦ le_trans (by rw [nth_termBVVec h hi]) (nth_le_listMax (i := i) (by simp [h, hi]))⟩

lemma IsSemitermVec.iff {k n v : V} : IsSemitermVec L k n v ↔ (len v = k ∧ ∀ i < k, IsSemiterm L n v.[i]) := by
  constructor
  · intro h; exact ⟨h.lh, fun i hi ↦ h.nth hi⟩
  · intro ⟨hk, h⟩; exact ⟨⟨hk.symm, fun i hi ↦ h i hi |>.isUTerm⟩, fun hi ↦ h _ hi |>.bv⟩

@[simp] lemma IsSemiterm.bvar {n z : V} :
    IsSemiterm L n ^#z ↔ z < n := by simp [IsSemiterm.def, succ_le_iff_lt]

@[simp] lemma IsSemiterm.fvar (n x : V) :
    IsSemiterm L n ^&x := by simp [IsSemiterm.def]

@[simp] lemma IsSemiterm.func {n k f v : V} :
    IsSemiterm L n (^func k f v) ↔ L.IsFunc k f ∧ IsSemitermVec L k n v := by
  simp only [IsSemiterm.def, IsUTerm.func_iff]
  constructor
  · rintro ⟨⟨hf, hbv⟩, hv⟩
    exact ⟨hf, hbv, by
      intro i hi
      have : listMax (termBVVec L k v) ≤ n := by simpa [termBV_func, hf, hbv] using hv
      simpa [hbv, hi] using listMaxss_le_iff.mp this i (by simp [hbv, hi])⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨hf, h.isUTerm⟩, by
      simp only [hf, h.isUTerm, termBV_func]
      apply listMaxss_le_iff.mpr
      intro i hi
      have hi : i < k := by simpa [hf, h.isUTerm] using hi
      simpa [hf, h.isUTerm, hi] using (h.nth hi).bv⟩

@[simp] lemma IsSemitermVec.empty (n : V) : IsSemitermVec L 0 n 0 := ⟨by simp, by simp⟩

@[simp] lemma IsSemitermVec.empty_iff {n : V} : IsSemitermVec L 0 n v ↔ v = 0 := by
  constructor
  · intro h; exact len_zero_iff_eq_nil.mp h.lh
  · rintro rfl; simp

@[simp] lemma IsSemitermVec.cons_iff {n w t : V} :
    IsSemitermVec L (k + 1) n (t ∷ w) ↔ IsSemiterm L n t ∧ IsSemitermVec L k n w := by
  constructor
  · intro h
    exact ⟨by simpa using h.nth (i := 0) (by simp),
      IsSemitermVec.iff.mpr ⟨by simpa using h.lh, fun i hi ↦ by simpa using h.nth (show i + 1 < k + 1 by simp [hi])⟩⟩
  · rintro ⟨ht, hw⟩
    exact ⟨hw.isUTerm.adjoin ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simpa using hw.nth (by simpa using hi) |>.bv⟩

lemma SemitermVec.adjoin {n m w t : V} (h : IsSemitermVec L n m w) (ht : IsSemiterm L m t) : IsSemitermVec L (n + 1) m (t ∷ w) :=
  IsSemitermVec.cons_iff.mpr ⟨ht, h⟩

@[simp] lemma IsSemitermVec.singleton {n t : V} :
    IsSemitermVec L 1 n ?[t] ↔ IsSemiterm L n t := by
  rw [show (1 : V) = 0 + 1 by simp, IsSemitermVec.cons_iff]; simp

@[simp] lemma IsSemitermVec.doubleton {n t₁ t₂ : V} :
    IsSemitermVec L 2 n ?[t₁, t₂] ↔ IsSemiterm L n t₁ ∧ IsSemiterm L n t₂ := by
  rw [show (2 : V) = 1 + 1 by simp [one_add_one_eq_two], IsSemitermVec.cons_iff]; simp

section

instance IsSemiterm.defined : 𝚫₁-Relation (IsSemiterm (V := V) L) via (isSemiterm L) := .mk <| by
  refine ⟨?_, ?_⟩
  · intro v
    simp [isSemiterm, HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSemiterm, IsSemiterm.def, HierarchySymbol.Semiformula.val_sigma]

instance IsSemiterm.definable : 𝚫₁-Relation (IsSemiterm (V := V) L) := IsSemiterm.defined.to_definable

instance IsSemiterm.definable' (Γ m) : Γ-[m + 1]-Relation (IsSemiterm (V := V) L) := IsSemiterm.definable.of_deltaOne

instance IsSemitermVec.defined : 𝚫₁-Relation₃ (IsSemitermVec (V := V) L) via (isSemitermVec L) := .mk <| by
  refine ⟨?_, ?_⟩
  · intro v
    simp [isSemitermVec, HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSemitermVec, IsSemitermVec.def, HierarchySymbol.Semiformula.val_sigma]

instance IsSemitermVec.definable : 𝚫₁-Relation₃ (IsSemitermVec (V := V) L) := IsSemitermVec.defined.to_definable

instance IsSemitermVec.definable' (Γ m) : Γ-[m + 1]-Relation₃ (IsSemitermVec (V := V) L) := IsSemitermVec.definable.of_deltaOne

end

lemma IsSemiterm.case_iff {n t : V} :
    IsSemiterm L n t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.IsFunc k f ∧ IsSemitermVec L k n v ∧ t = ^func k f v) := by
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

alias ⟨IsSemiterm.case, IsSemiterm.mk'⟩ := IsSemiterm.case_iff

lemma IsSemiterm.induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.IsFunc k f → IsSemitermVec L k n v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, IsSemiterm L n t → P t := by
  intro t ht
  suffices IsSemiterm L n t → P t by exact this ht
  apply IsUTerm.induction Γ ?_ ?_ ?_ ?_ t ht.isUTerm
  · definability
  · intro z; simp only [bvar]; exact hbvar z
  · intro x _; exact hfvar x
  · intro k f v hf _ ih h
    have hv : IsSemitermVec L k n v := by simp_all
    exact hfunc k f v hf hv (fun i hi ↦ ih i hi (hv.nth hi))

@[simp] lemma IsSemitermVec.nil (k : V): IsSemitermVec L 0 k 0 := ⟨by simp, by simp⟩

@[simp] lemma IsSemitermVec.adjoin {k n w t : V} (h : IsSemitermVec L n k w) (ht : IsSemiterm L k t) : IsSemitermVec L (n + 1) k (t ∷ w) :=
  ⟨h.isUTerm.adjoin ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simp [h.bv (by simpa using hi)]⟩

lemma IsSemiterm.sigma1_induction {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.IsFunc k f → IsSemitermVec L k n v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, IsSemiterm L n t → P t := IsSemiterm.induction _ hP hbvar hfvar hfunc

end isSemiterm

end LO.FirstOrder.Arithmetic.Bootstrapping
