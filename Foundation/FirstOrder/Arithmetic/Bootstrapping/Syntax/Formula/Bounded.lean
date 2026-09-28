module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Internal $\Delta_0$ formulas

The internal predicate `IsBounded` on codes of bounded arithmetical formulas: it is
`𝚫ᴬ₁`-definable, closed under negation and shift, and agrees with `ℬ[<, ℒₒᵣ].Closure` on
quoted formulas.

## References

- [HP98, 0.30, Lemma I.1.68]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Internal bounded existential quantifier `qqBex` -/

section qqBex

noncomputable def qqBex (u q : V) : V := ^∃ ((^#0 ^< u) ^⋏ q)

@[simp] lemma lt_q_qqBex (u q : V) : q < qqBex u q := lt_trans (lt_K!_right _ _) (lt_exists _)

@[simp] lemma lt_u_qqBex (u q : V) : u < qqBex u q :=
  lt_trans (Arithmetic.lt_qqLT_right _ _) (lt_trans (lt_K!_left _ _) (lt_exists _))

def _root_.FFL.FirstOrder.Arithmetic.qqBexDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ lt, !qqLTDef lt bv u ∧ ∃ g, !qqAndDef g lt q ∧ !qqExsDef p g”

instance qqBex_defined : 𝚺ᴬ₁-Function₂ (qqBex : V → V → V) via qqBexDef := .mk fun v ↦ by
  simp [qqBexDef, qqBex, Arithmetic.qqLT_defined.df]

instance qqBex_definable (Γ m) : Γᴬ-[m + 1]-Function₂ (qqBex : V → V → V) :=
  .of_sigmaOne qqBex_defined.to_definable

variable {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q)
include hu hq

lemma neg_qqBall : neg ℒₒᵣ (qqBall u q) = qqBex u (neg ℒₒᵣ q) := by
  simp [qqBall, qqBex, Arithmetic.qqNLT, Arithmetic.qqLT, hu, hq];

lemma neg_qqBex : neg ℒₒᵣ (qqBex u q) = qqBall u (neg ℒₒᵣ q) := by
  simp [qqBall, qqBex, Arithmetic.qqNLT, Arithmetic.qqLT, hu, hq];

lemma shift_qqBall : shift ℒₒᵣ (qqBall u q) = qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  simp [qqBall, Arithmetic.qqNLT, hu, hq];

lemma shift_qqBex : shift ℒₒᵣ (qqBex u q) = qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  simp [qqBex, Arithmetic.qqLT, hu, hq];

end qqBex

/-! ## Internal $\Delta_0$ predicate `IsBounded` -/

section isBounded

namespace IsBoundedF

def Phi (C : Set V) (p : V) : Prop :=
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ k r v, p = ^rel k r v) ∨
  (∃ k r v, p = ^nrel k r v) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBex u q)

private lemma phi_iff (C p : V) :
    Phi {x | x ∈ C} p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^nrel k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBex u q) where
  mp := by
    rintro (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩);
    · disj 1; rfl;
    · disj 2; rfl;
    · disj 3; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩;
    · disj 4; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩;
    · disj 5; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 6; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · disj 7;
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBall _ _, q, lt_q_qqBall _ _,
        ⟨t, (le_termBShift ht).trans_lt (lt_u_qqBall _ _), ht, rfl⟩, hq, rfl⟩;
    · disj 8;
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBex _ _, q, lt_q_qqBex _ _,
        ⟨t, (le_termBShift ht).trans_lt (lt_u_qqBex _ _), ht, rfl⟩, hq, rfl⟩;
  mpr := by
    unfold Phi;
    rintro (rfl | rfl | ⟨k, _, r, _, v, _, rfl⟩ | ⟨k, _, r, _, v, _, rfl⟩
      | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩) <;> grind;

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBallDef p u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBexDef p u q)”)
  (.mkPi “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p,
      (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
      q ∈ C ∧ ∀ p', !qqBallDef p' u q → p = p') ∨
    (∃ u < p, ∃ q < p,
      (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
      q ∈ C ∧ ∀ p', !qqBexDef p' u q → p = p')”)⟩

def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor;
    · intro v;
      simp [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df];
    · intro v;
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df]
        using (phi_iff _ _).symm;
  monotone := by
    unfold Phi;
    intro C C' hC _ x;
    grind;

instance : construction.StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩) <;>
      grind [lt_K!_left, lt_K!_right, lt_or_left, lt_or_right, lt_q_qqBall, lt_q_qqBex];

end IsBoundedF

def IsBounded (p : V) : Prop := IsBoundedF.construction.Fixpoint ![] p

noncomputable def isBounded : 𝚫ᴬ₁.Semisentence 1 := IsBoundedF.blueprint.fixpointDefΔ₁

instance IsBounded.defined : 𝚫ᴬ₁-Predicate (IsBounded (V := V)) via isBounded :=
  IsBoundedF.construction.fixpoint_definedΔ₁

instance IsBounded.definable : 𝚫ᴬ₁-Predicate (IsBounded : V → Prop) :=
  IsBounded.defined.to_definable

lemma IsBounded.case_iff {p : V} :
    IsBounded p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨
    (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBex u q) :=
  IsBoundedF.construction.case

alias ⟨IsBounded.case, IsBounded.mk⟩ := IsBounded.case_iff

@[simp] lemma IsBounded.verum : IsBounded (V := V) (^⊤) := IsBounded.mk <| by disj 1; rfl
@[simp] lemma IsBounded.falsum : IsBounded (V := V) (^⊥) := IsBounded.mk <| by disj 2; rfl

@[simp] lemma IsBounded.rel {k r v : V} : IsBounded (^rel k r v) :=
  IsBounded.mk <| by disj 3; exact ⟨k, r, v, rfl⟩

@[simp] lemma IsBounded.nrel {k r v : V} : IsBounded (^nrel k r v) :=
  IsBounded.mk <| by disj 4; exact ⟨k, r, v, rfl⟩

@[simp] lemma IsBounded.and_iff {p q : V} : IsBounded (p ^⋏ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor;
  · intro h;
    rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
      simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
  · rintro ⟨hp, hq⟩;
    exact IsBounded.mk <| by disj 5; exact ⟨p, q, hp, hq, rfl⟩;

@[simp] lemma IsBounded.or_iff {p q : V} : IsBounded (p ^⋎ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor;
  · intro h;
    rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
      simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex];
  · rintro ⟨hp, hq⟩;
    exact IsBounded.mk <| by disj 6; exact ⟨p, q, hp, hq, rfl⟩;

lemma IsBounded.ball {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBall (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by disj 7; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsBounded.bex {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBex (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by disj 8; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsBounded.of_all {p : V} (h : IsBounded (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q
      ∧ p = qqOr (Arithmetic.qqNLT (qqBvar 0) u) q := by
  rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, _, ht, hq, h⟩ | ⟨_, _, _, _, h⟩) <;>
    simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex,
      Arithmetic.qqNLT];

lemma IsBounded.of_ex {p : V} (h : IsBounded (^∃ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q
      ∧ p = (Arithmetic.qqLT (qqBvar 0) u) ^⋏ q := by
  rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, _, _, _, h⟩ | ⟨_, _, ht, hq, h⟩) <;>
    simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex,
      Arithmetic.qqLT];

lemma IsBounded.induction (Γ : Polarity) {P : V → Prop} (hP : Γᴬ-[1]-Predicate P)
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hrel : ∀ k r v, P (^rel k r v)) (hnrel : ∀ k r v, P (^nrel k r v))
    (hand : ∀ p q, IsBounded p → IsBounded q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsBounded p → IsBounded q → P p → P q → P (p ^⋎ q))
    (hball : ∀ t q, IsUTerm ℒₒᵣ t → IsBounded q → P q → P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, IsUTerm ℒₒᵣ t → IsBounded q → P q → P (qqBex (termBShift ℒₒᵣ t) q)) :
    ∀ p, IsBounded p → P p :=
  IsBoundedF.construction.induction (v := ![]) hP (by
    rintro C hC x (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p, q, hp, hq, rfl⟩
      | ⟨p, q, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩);
    · exact hverum;
    · exact hfalsum;
    · exact hrel k r v;
    · exact hnrel k r v;
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2;
    · exact hball t q ht (hC q hq).1 (hC q hq).2;
    · exact hbex t q ht (hC q hq).1 (hC q hq).2)

lemma IsBounded.neg {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (Bootstrapping.neg ℒₒᵣ p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p) from
    this p h hp;
  apply IsBounded.induction 𝚺
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p)) (by definability)
    (by simp) (by simp) (by simp +contextual) (by simp +contextual) (by simp +contextual)
    (by simp +contextual);
  · intro t q ht _ ih h;
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall];
    simpa [neg_qqBall ht.termBShift hq] using IsBounded.bex ht (ih hq);
  · intro t q ht _ ih h;
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex];
    simpa [neg_qqBex ht.termBShift hq] using IsBounded.ball ht (ih hq);

lemma IsBounded.shift {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (Bootstrapping.shift ℒₒᵣ p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p) from
    this p h hp;
  apply IsBounded.induction 𝚺
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p)) (by definability)
    (by simp) (by simp) (by simp +contextual) (by simp +contextual) (by simp +contextual)
    (by simp +contextual);
  · intro t q ht _ ih h;
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall];
    simpa [shift_qqBall ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      using IsBounded.ball ht.termShift (ih hq);
  · intro t q ht _ ih h;
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex];
    simpa [shift_qqBex ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      using IsBounded.bex ht.termShift (ih hq);

end isBounded

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Correctness of `IsBounded`: `IsBounded ⌜ψ⌝ ↔ ℬ[<, ℒₒᵣ].Closure ψ` -/

section correctness

open Bootstrapping

variable {n : ℕ}

lemma quote_bex (t : SyntacticSemiterm ℒₒᵣ n) (φ : ArithmeticSemiproposition (n + 1)) :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemiproposition n)⌝ : ℕ)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.bexs_eq];
  simp only [Semiformula.Operator.lt_def, Semiformula.quote_ex,
    Semiformula.quote_and, qqBex, qqExs_inj, qqAnd_inj, and_true];
  simp [Semiformula.quote_rel, Arithmetic.qqLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one];
  rfl;

lemma exists_ball_of_quote_eq {φ : ArithmeticSemiproposition (n + 1)} {t q : ℕ}
    (ht : IsUTerm ℒₒᵣ t) (h : (⌜φ⌝ : ℕ) = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) :
    ∃ (s : SyntacticSemiterm ℒₒᵣ n) (ψ : ArithmeticSemiproposition (n + 1)),
      φ = “#0 < !!(Rew.bShift s)” 🡒 ψ := by
  have hsf : IsSemiformula ℒₒᵣ (n + 1) ((^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
    simpa [h] using Semiformula.quote_isSemiformula (V := ℕ) φ;
  obtain ⟨h₁, hq⟩ := IsSemiformula.or.mp hsf;
  obtain ⟨ψ, rfl⟩ := IsSemiformula.sound hq;
  have ht' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) := by
    simpa using (IsSemiformula.nrel.mp h₁).2.nth (i := 1) (by simp);
  obtain ⟨s, rfl⟩ := IsSemiterm.sound <| IsSemiterm.def.mpr
    ⟨ht, (termBV_termBShift_le ht _).mp (IsSemiterm.def.mp ht').2⟩;
  have e : (∀¹ φ) = ∀¹[“#0 < !!(Rew.bShift s)”] ψ := by
    apply Semiformula.quote_inj_iff (V := ℕ) |>.mp;
    rw [Semiformula.quote_all, h, quote_ball];
    rfl;
  exact ⟨s, ψ, (Semiformula.all_inj _ _).mp e⟩;

lemma exists_bex_of_quote_eq {φ : ArithmeticSemiproposition (n + 1)} {t q : ℕ}
    (ht : IsUTerm ℒₒᵣ t) (h : (⌜φ⌝ : ℕ) = (^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) :
    ∃ (s : SyntacticSemiterm ℒₒᵣ n) (ψ : ArithmeticSemiproposition (n + 1)),
      φ = “#0 < !!(Rew.bShift s)” ⋏ ψ := by
  have hsf : IsSemiformula ℒₒᵣ (n + 1) ((^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) := by
    simpa [h] using Semiformula.quote_isSemiformula (V := ℕ) φ;
  obtain ⟨h₁, hq⟩ := IsSemiformula.and.mp hsf;
  obtain ⟨ψ, rfl⟩ := IsSemiformula.sound hq;
  have ht' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) := by
    simpa using (IsSemiformula.rel.mp h₁).2.nth (i := 1) (by simp);
  obtain ⟨s, rfl⟩ := IsSemiterm.sound <| IsSemiterm.def.mpr
    ⟨ht, (termBV_termBShift_le ht _).mp (IsSemiterm.def.mp ht').2⟩;
  have e : (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift s)”] ψ := by
    apply Semiformula.quote_inj_iff (V := ℕ) |>.mp;
    rw [Semiformula.quote_ex, h, quote_bex];
    rfl;
  exact ⟨s, ψ, (Semiformula.exs_inj _ _).mp e⟩;

private lemma isBounded_of_bounded {ψ : ArithmeticSemiproposition n}
    (h : ℬ[<, ℒₒᵣ].Closure ψ) : IsBounded (⌜ψ⌝ : ℕ) := by
  revert h;
  apply Bounding.Closure.arithmetic_induction (P := fun _ φ ↦ IsBounded (⌜φ⌝ : ℕ)) (by simp)
    (by simp) (by simp [Semiformula.quote_rel]) (by simp [Semiformula.quote_nrel])
    (by simp [Semiformula.quote_rel]) (by simp [Semiformula.quote_nrel])
    (by simp +contextual [Semiformula.quote_and]) (by simp +contextual [Semiformula.quote_or]);
  · intro n t φ _ ih;
    rw [quote_ball];
    exact IsBounded.ball (by simp [Semiterm.quote_def]) ih;
  · intro n t φ _ ih;
    rw [quote_bex];
    exact IsBounded.bex (by simp [Semiterm.quote_def]) ih;

private lemma bounded_of_isBounded (ψ : ArithmeticSemiproposition n) :
    IsBounded (⌜ψ⌝ : ℕ) → ℬ[<, ℒₒᵣ].Closure ψ := by
  induction ψ using Semiformula.rec' with
  | hverum => simp;
  | hfalsum => simp;
  | hrel => simp;
  | hnrel => simp;
  | hand φ ψ ihφ ihψ => simp +contextual [Semiformula.quote_and, ihφ, ihψ];
  | hor φ ψ ihφ ihψ => simp +contextual [Semiformula.quote_or, ihφ, ihψ];
  | hall φ ih =>
    intro h;
    rw [Semiformula.quote_all] at h;
    obtain ⟨_, q, ⟨t, ht, rfl⟩, hq, hφ⟩ := IsBounded.of_all h;
    obtain ⟨s, ψ, rfl⟩ := exists_ball_of_quote_eq ht hφ;
    have : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift s)” 🡒 ψ) :=
      ih (by simp [hφ, hq, Arithmetic.qqNLT]);
    exact .ball rfl (Rew.positive_iff.mpr ⟨s, rfl⟩) (Bounding.Closure.or_iff.mp this).2;
  | hexs φ ih =>
    intro h;
    rw [Semiformula.quote_ex] at h;
    obtain ⟨_, q, ⟨t, ht, rfl⟩, hq, hφ⟩ := IsBounded.of_ex h;
    obtain ⟨s, ψ, rfl⟩ := exists_bex_of_quote_eq ht hφ;
    have : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift s)” ⋏ ψ) :=
      ih (by simp [hφ, hq, Arithmetic.qqLT]);
    exact .bexs rfl (Rew.positive_iff.mpr ⟨s, rfl⟩) (Bounding.Closure.and_iff.mp this).2;

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma isBounded_quote_iff_s (ψ : ArithmeticSemiproposition n) :
    IsBounded (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Closure ψ := by
  have h : IsBounded (⌜ψ⌝ : V) ↔ IsBounded (⌜ψ⌝ : ℕ) := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton,
      (IsBounded.defined (V := V)).df, (IsBounded.defined (V := ℕ)).df]
      using models_iff_of_Delta1 (V := V) IsBounded.defined.proper IsBounded.defined.proper
        (e := ![⌜ψ⌝]);
  exact h.trans ⟨bounded_of_isBounded ψ, isBounded_of_bounded⟩;

theorem isBounded_quote_iff (σ : ArithmeticSemisentence n) :
    IsBounded (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Closure σ := by
  simp [Sentence.quote_def, isBounded_quote_iff_s];

end correctness

end FFL.FirstOrder.Arithmetic
