import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Derivation

/-!

# Formalized Theory

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section theory

variable (L)

structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  ch : HSemisentence ℒₒᵣ 1 𝚺₁

protected structure Language.Theory where
  set : Set V
  set_fvFree : ∀ p ∈ set, L.IsFVFree 0 p

instance : Membership V L.Theory := ⟨fun x T ↦ x ∈ T.set⟩

variable {L}

namespace Language.Theory

protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : 𝚺₁-Predicate (· ∈ T.set) via pT.ch

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

instance mem_defined : 𝚺₁-Predicate (· ∈ T) via pT.ch := Defined.defined

instance mem_definable : 𝚺₁-Predicate (· ∈ T) := Defined.defined.to_definable

variable {T}

lemma fvFree_neg_of_mem {p} (hp : p ∈ T) : L.IsFVFree 0 (L.neg p) := by simpa using T.set_fvFree p hp

lemma fvFree_of_neg_mem {p} (hp : L.neg p ∈ T) : L.IsFVFree 0 p := by simpa using T.set_fvFree _ hp

end Language.Theory

end theory

section derivableWithTheory

def Language.Theory.Derivable (T : L.Theory) (s : V) : Prop :=
  ∃ antecedents : V, (∀ p ∈ antecedents, L.neg p ∈ T) ∧ L.Derivable (antecedents ∪ s)

def Language.Theory.Provable (T : L.Theory) (p : V) : Prop := T.Derivable {p}

section

def _root_.LO.FirstOrder.Arith.LDef.TDef.derivableDef {pL : LDef} (pT : pL.TDef) : 𝚺₁-Semisentence 1 := .mkSigma
  “s | ∃ a, (∀ p ∈' a, ∃ np, !pL.negDef np p ∧ !pT.ch np) ∧ ∃ uni, !unionDef uni a s ∧ !pL.derivableDef uni” (by simp)

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

protected lemma Language.Theory.derivable_defined : 𝚺₁-Predicate T.Derivable via pT.derivableDef := by
  intro v; simp [LDef.TDef.derivableDef, (neg_defined L).df.iff,
    (T.mem_defined).df.iff, (derivable_defined L).df.iff, Language.Theory.Derivable]

instance Language.Theory.derivable_definable : 𝚺₁-Predicate T.Derivable := Defined.to_definable _ T.derivable_defined

/-- instance for definability tactic-/
@[simp] instance Language.Theory.derivable_definable' : (𝚺, 0 + 1)-Predicate T.Derivable := T.derivable_definable

def _root_.LO.FirstOrder.Arith.LDef.TDef.prv {pL : LDef} (pT : pL.TDef) : 𝚺₁-Semisentence 1 := .mkSigma
  “p | ∃ s, !insertDef s p 0 ∧ !pT.derivableDef s” (by simp)

protected lemma Language.Theory.provable_defined : 𝚺₁-Predicate T.Provable via pT.prv := by
  intro v; simp [LDef.TDef.prv, (T.derivable_defined).df.iff, Language.Theory.Provable, singleton_eq_insert, emptyset_def]

instance Language.Theory.provable_definable : 𝚺₁-Predicate T.Provable := Defined.to_definable _ T.provable_defined

/-- instance for definability tactic-/
@[simp] instance Language.Theory.provable_definable' : (𝚺, 0 + 1)-Predicate T.Provable := T.provable_definable

end

namespace Language.Theory.Derivable

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT]

lemma formulaSet {s : V} (h : T.Derivable s) : L.FormulaSet s := by
  rcases h with ⟨t, _, h⟩;
  simp [by simpa using h.formulaSet]

lemma ofSetEq {s s' : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : T.Derivable s') :
    T.Derivable s := by
  have : s' = s := mem_ext h
  rcases this; exact hd

lemma by_axm (hs : L.FormulaSet s) {p} (hpT : p ∈ T) (hp : p ∈ s) : T.Derivable s :=
  ⟨{L.neg p}, by simp [neg_neg (hs p hp), hpT], Language.Derivable.em (p := p) (by simp [hs, hs p hp]) (by simp [hp]) (by simp)⟩

lemma verum (hs : L.FormulaSet s) (h : ^⊤ ∈ s) : T.Derivable s :=
  ⟨∅, by simp, Language.Derivable.verum (by simp [hs]) (by simp [h])⟩

lemma em (hs : L.FormulaSet s) (p : V) (h : p ∈ s) (hn : L.neg p ∈ s) : T.Derivable s :=
  ⟨∅, by simp, Language.Derivable.em (p := p) (by simpa) (by simp [h]) (by simp [hn])⟩

lemma and {p q : V} (dp : T.Derivable (insert p s)) (dq : T.Derivable (insert q s)) : T.Derivable (insert (p ^⋏ q) s) := by
  rcases dp with ⟨Γ, hΓ, dp⟩
  rcases dq with ⟨Δ, hΔ, dq⟩
  exact ⟨Γ ∪ Δ, by intro x hx; rcases mem_cup_iff.mp hx with (hx | hx); { exact hΓ x hx }; { exact hΔ x hx },
    Language.Derivable.and_m (p := p) (q := q) (by simp)
      (Language.Derivable.wk (by simp [by simpa using dp.formulaSet, by simpa using dq.formulaSet])
        (by intro x; simp; tauto) dp)
      (Language.Derivable.wk (by simp [by simpa using dp.formulaSet, by simpa using dq.formulaSet])
        (by intro x; simp; tauto) dq)⟩

lemma or {p q : V} (dpq : T.Derivable (insert p (insert q s))) : T.Derivable (insert (p ^⋎ q) s) := by
  rcases dpq with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, Language.Derivable.or_m (p := p) (q := q) (by simp)
    (d.wk (by simp [by simpa using d.formulaSet]) <| by intro x; simp; tauto)⟩

lemma all {p : V} (hp : L.Semiformula 1 p) (dp : T.Derivable (insert (L.free p) (L.setShift s))) : T.Derivable (insert (^∀ p) s) := by
  rcases dp with ⟨Γ, hΓ, d⟩
  have hs : L.setShift Γ = Γ := mem_ext <| by
    simp only [mem_setShift_iff]; intro x
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa [fvFree_of_neg_mem (hΓ x hx) |>.2] using hx
    · intro hx; exact ⟨x, hx, by simp [fvFree_of_neg_mem (hΓ x hx) |>.2]⟩
  exact ⟨Γ, hΓ,
    Language.Derivable.all_m (p := p) (by simp)
      (Language.Derivable.wk (by simp [by simpa using d.formulaSet, hp])
        (by intro x; simp [hs]; tauto) d)⟩

lemma ex {p t : V} (hp : L.Semiformula 1 p) (ht : L.Term t)
    (dp : T.Derivable (insert (L.substs₁ t p) s)) : T.Derivable (insert (^∃ p) s) := by
  rcases dp with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, Language.Derivable.ex_m (p := p) (by simp) ht
    (Language.Derivable.wk (by simp [by simpa using d.formulaSet, hp]) (by intro x; simp; tauto) d)⟩

lemma wk {s s' : V} (h : L.FormulaSet s) (hs : s' ⊆ s) (d : T.Derivable s') : T.Derivable s := by
  rcases d with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, Language.Derivable.wk (by simp [by simpa using d.formulaSet, h]) (by intro x; simp; tauto) d⟩

lemma shift {s : V} (d : T.Derivable s) : T.Derivable (L.setShift s) := by
  rcases d with ⟨Γ, hΓ, d⟩
  have hs : L.setShift Γ = Γ := mem_ext <| by
    simp only [mem_setShift_iff]; intro x
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa [fvFree_of_neg_mem (hΓ x hx) |>.2] using hx
    · intro hx; exact ⟨x, hx, by simp [fvFree_of_neg_mem (hΓ x hx) |>.2]⟩
  exact ⟨Γ, hΓ, by simpa [hs] using Language.Derivable.shift d⟩

lemma cut {s : V} (p : V) (d : T.Derivable (insert p s)) (dn : T.Derivable (insert (L.neg p) s)) : T.Derivable s := by
  rcases d with ⟨Γ, hΓ, d⟩; rcases dn with ⟨Δ, hΔ, b⟩
  exact ⟨Γ ∪ Δ, fun p hp ↦ by rcases mem_cup_iff.mp hp with (h | h); { exact hΓ p h }; { exact hΔ p h },
    Language.Derivable.cut p
      (Language.Derivable.wk
        (by simp [by simpa using d.formulaSet, by simpa using b.formulaSet]) (by intro x; simp; tauto) d)
      (Language.Derivable.wk
        (by simp [by simpa using d.formulaSet, by simpa using b.formulaSet]) (by intro x; simp; tauto) b)⟩

/-- Crucial inducion for formalized $\Sigma_1$-completeness. -/
lemma conj (ps : V) {s} (hs : L.FormulaSet s)
    (ds : ∀ i < len ps, T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋀ ps) s) := by
  have : ∀ k ≤ len ps, T.Derivable (insert (^⋀ (takeLast ps k)) s) := by
    intro k hk
    induction k using induction_iSigmaOne
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
    induction k using induction_iSigmaOne
    · apply Definable.imp (by definability)
      apply Definable.ball_le (by definability)
      apply Definable.imp (by definability)
      apply Definable.imp (by definability)
      definability
    case zero =>
      intro s' _ ss hs'
      refine wk ?_ ?_ d
      · simp [by simpa using d.formulaSet]
        intro x hx
        exact d.formulaSet x (by simp [ss hx])
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

lemma disj (ps s : V) {i} (hps : ∀ i < len ps, L.Formula ps.[i])
  (hi : i < len ps) (d : T.Derivable (insert ps.[i] s)) : T.Derivable (insert (^⋁ ps) s) :=
  disjDistr ps s <| wk
    (by simp [by simpa using d.formulaSet]; intro x hx; rcases mem_vecToSet_iff.mp hx with ⟨i, hi, rfl⟩; exact hps i hi)
    (by
      intro x; simp only [mem_bitInsert_iff, mem_cup_iff]
      rintro (rfl | hx)
      · left; exact mem_vecToSet_iff.mpr ⟨i, hi, rfl⟩
      · right; exact hx) d

end Language.Theory.Derivable

end derivableWithTheory

end LO.Arith
