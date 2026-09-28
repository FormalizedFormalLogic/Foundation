module

public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# Internal $\Delta_0$ formulas

This module introduces the bounded-existential coding operation and the internal shape
predicate `IsBounded` for $\Delta_0$ formulas, built as a least fixpoint in the manner of
`IsSigma1`, and proves that it agrees with the external class `ℬ[<, ℒₒᵣ].Closure` on quoted
formulas.

## References

- [HP98, 0.30, Lemma I.1.68]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def qqBex (u q : V) : V := ^∃ ((^#0 ^< u) ^⋏ q)

@[simp] lemma lt_q_qqBex (u q : V) : q < qqBex u q := lt_trans (lt_K!_right _ _) (lt_exists _)
@[simp] lemma lt_u_qqBex (u q : V) : u < qqBex u q :=
  lt_trans (Arithmetic.lt_qqLT_right _ _) (lt_trans (lt_K!_left _ _) (lt_exists _))

def _root_.FFL.FirstOrder.Arithmetic.qqBexDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ lt, !qqLTDef lt bv u ∧ ∃ g, !qqAndDef g lt q ∧ !qqExsDef p g”

instance qqBex_defined : 𝚺ᴬ₁-Function₂ (qqBex : V → V → V) via qqBexDef := .mk fun v ↦ by
  simp [qqBexDef, qqBex, (Arithmetic.qqLT_defined (V := V)).df]
instance qqBex_definable (Γ m) : Γᴬ-[m + 1]-Function₂ (qqBex : V → V → V) :=
  .of_sigmaOne qqBex_defined.to_definable

lemma neg_qqBall {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBall u q) = qqBex u (neg ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqNLT (qqBvar 0) u) := by simp [Arithmetic.qqNLT, hu]
  rw [show qqBall u q = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ q) from rfl,
    show qqBex u (neg ℒₒᵣ q) = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ neg ℒₒᵣ q) from rfl,
    neg_all (by simp [hlt, hq]), neg_or hlt hq];
  simp [Arithmetic.qqNLT, Arithmetic.qqLT, hu];

lemma neg_qqBex {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBex u q) = qqBall u (neg ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqLT (qqBvar 0) u) := by simp [Arithmetic.qqLT, hu]
  rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl,
    show qqBall u (neg ℒₒᵣ q) = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ neg ℒₒᵣ q) from rfl,
    neg_ex (by simp [hlt, hq]), neg_and hlt hq];
  simp [Arithmetic.qqNLT, Arithmetic.qqLT, hu];

namespace IsBoundedF

def Phi (C : Set V) (p : V) : Prop := (p = ^⊤) ∨ (p = ^⊥) ∨ (∃ k r v, p = ^rel k r v) ∨
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
    · tauto;
    · tauto;
    · iterate 2 right;
      left; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩;
    · iterate 3 right;
      left; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩;
    · iterate 4 right;
      left; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · iterate 5 right;
      left; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩;
    · iterate 6 right;
      left;
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBall _ _, q, lt_q_qqBall _ _,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (lt_u_qqBall _ _), ht, rfl⟩, hq, rfl⟩;
    · iterate 7 right;
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBex _ _, q, lt_q_qqBex _ _,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (lt_u_qqBex _ _), ht, rfl⟩, hq, rfl⟩;
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
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df];
    · intro v;
      symm;
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df]
        using phi_iff (V := V) _ _;
  monotone := by
    unfold Phi;
    rintro C C' hC _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩) <;> grind;

instance : construction.StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩);
    · left; exact h;
    · right; left; exact h;
    · iterate 2 right;
      left; exact h;
    · iterate 3 right;
      left; exact h;
    · iterate 4 right;
      left; exact ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩;
    · iterate 5 right;
      left; exact ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩;
    · iterate 6 right;
      left; exact ⟨u, q, ht, ⟨hq, lt_q_qqBall _ _⟩, rfl⟩;
    · iterate 7 right;
      exact ⟨u, q, ht, ⟨hq, lt_q_qqBex _ _⟩, rfl⟩;

end IsBoundedF

lemma shift_qqBall {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    shift ℒₒᵣ (qqBall u q) = qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqNLT (qqBvar 0) u) := by simp [Arithmetic.qqNLT, hu]
  rw [show qqBall u q = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ q) from rfl,
    show qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q)
      = ^∀ ((Arithmetic.qqNLT (qqBvar 0) (termShift ℒₒᵣ u)) ^⋎ shift ℒₒᵣ q) from rfl,
    shift_all (by simp [hlt, hq]), shift_or hlt hq];
  simp [Arithmetic.qqNLT, hu];

lemma shift_qqBex {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    shift ℒₒᵣ (qqBex u q) = qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqLT (qqBvar 0) u) := by simp [Arithmetic.qqLT, hu]
  rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl,
    show qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q)
      = ^∃ ((Arithmetic.qqLT (qqBvar 0) (termShift ℒₒᵣ u)) ^⋏ shift ℒₒᵣ q) from rfl,
    shift_exs (by simp [hlt, hq]), shift_and hlt hq];
  simp [Arithmetic.qqLT, hu];

def IsBounded (p : V) : Prop := IsBoundedF.construction.Fixpoint ![] p

noncomputable def isBounded : 𝚫ᴬ₁.Semisentence 1 := IsBoundedF.blueprint.fixpointDefΔ₁

instance IsBounded.defined : 𝚫ᴬ₁-Predicate (IsBounded (V := V)) via isBounded :=
  IsBoundedF.construction.fixpoint_definedΔ₁

instance IsBounded.definable : 𝚫ᴬ₁-Predicate (IsBounded : V → Prop) :=
  IsBounded.defined.to_definable

lemma IsBounded.case_iff {p : V} :
    IsBounded p ↔
    (p = ^⊤) ∨ (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨ (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBex u q) :=
  IsBoundedF.construction.case

alias ⟨IsBounded.case, IsBounded.mk⟩ := IsBounded.case_iff

@[simp] lemma IsBounded.verum : IsBounded (V := V) (^⊤) := IsBounded.mk <| by grind
@[simp] lemma IsBounded.falsum : IsBounded (V := V) (^⊥) := IsBounded.mk <| by grind
@[simp] lemma IsBounded.rel {k r v : V} : IsBounded (^rel k r v) := IsBounded.mk <| by grind
@[simp] lemma IsBounded.nrel {k r v : V} : IsBounded (^nrel k r v) := IsBounded.mk <| by grind

@[simp] lemma IsBounded.and_iff {p q : V} : IsBounded (p ^⋏ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor;
  · intro h;
    rcases h.case with
      (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ |
        ⟨_,_,_,_,h⟩) <;>
      simp only [qqAnd, qqVerum, qqFalsum, qqRel, qqNRel, qqOr, qqExs, qqBall, qqBex, qqAll,
        add_left_inj, pair_ext_iff, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and, true_and] at h;
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩;
  · rintro ⟨hp, hq⟩;
    exact IsBounded.mk <| by grind;

@[simp] lemma IsBounded.or_iff {p q : V} : IsBounded (p ^⋎ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor;
  · intro h;
    rcases h.case with
      (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,_,_,h⟩ |
        ⟨_,_,_,_,h⟩) <;>
      simp only [qqOr, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqExs, qqBall, qqBex, qqAll,
        add_left_inj, pair_ext_iff, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and, true_and] at h;
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩;
  · rintro ⟨hp, hq⟩;
    exact IsBounded.mk <| by grind;

lemma IsBounded.ball {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBall (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by grind

lemma IsBounded.bex {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBex (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by grind

lemma IsBounded.of_all {p : V} (h : IsBounded (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q
      ∧ p = qqOr (Arithmetic.qqNLT (qqBvar 0) u) q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩
    | ⟨u, q, hguard, hq, h⟩ | ⟨_,_,_,_,h⟩) <;>
    first
      | (simp [qqAll, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqExs, qqBex] at h
         done)
      | (rw [show qqBall u q = ^∀ (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q) from rfl,
            qqAll_inj] at h
         exact ⟨u, q, hguard, hq, h⟩)

lemma IsBounded.of_ex {p : V} (h : IsBounded (^∃ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q
      ∧ p = (Arithmetic.qqLT (qqBvar 0) u) ^⋏ q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩
    | ⟨_,_,_,_,h⟩ | ⟨u, q, hguard, hq, h⟩) <;>
    first
      | (simp [qqExs, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqBall] at h
         done)
      | (rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl,
            qqExs_inj] at h
         exact ⟨u, q, hguard, hq, h⟩)

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
  have H : ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p) := by
    apply IsBounded.induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p));
    · definability;
    · simp;
    · simp;
    · intro k r v h;
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h;
      simp [hr, hv];
    · intro k r v h;
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h;
      simp [hr, hv];
    · intro p q _ _ ihp ihq h;
      obtain ⟨hp, hq⟩ := IsUFormula.and.mp h;
      simp [hp, hq, ihp hp, ihq hq];
    · intro p q _ _ ihp ihq h;
      obtain ⟨hp, hq⟩ := IsUFormula.or.mp h;
      simp [hp, hq, ihp hp, ihq hq];
    · intro t q ht _ ih h;
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [neg_qqBall ht.termBShift hq];
      exact IsBounded.bex ht (ih hq);
    · intro t q ht _ ih h;
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [neg_qqBex ht.termBShift hq];
      exact IsBounded.ball ht (ih hq);
  exact H p h hp;

lemma IsBounded.shift {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (Bootstrapping.shift ℒₒᵣ p) := by
  have H : ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p) := by
    apply IsBounded.induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p));
    · definability;
    · simp;
    · simp;
    · intro k r v h;
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h;
      simp [hr, hv];
    · intro k r v h;
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h;
      simp [hr, hv];
    · intro p q _ _ ihp ihq h;
      obtain ⟨hp, hq⟩ := IsUFormula.and.mp h;
      simp [hp, hq, ihp hp, ihq hq];
    · intro p q _ _ ihp ihq h;
      obtain ⟨hp, hq⟩ := IsUFormula.or.mp h;
      simp [hp, hq, ihp hp, ihq hq];
    · intro t q ht _ ih h;
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [shift_qqBall ht.termBShift hq, ← termBShift_termShift ht.isSemiterm];
      exact IsBounded.ball ht.termShift (ih hq);
    · intro t q ht _ ih h;
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [shift_qqBex ht.termBShift hq, ← termBShift_termShift ht.isSemiterm];
      exact IsBounded.bex ht.termShift (ih hq);
  exact H p h hp;

lemma IsBounded.isSigma1 {p : V} (h : IsBounded p) : IsSigma1 p := by
  have : 𝚫ᴬ₁-Predicate (IsSigma1 : V → Prop) := IsSigma1.defined.to_definable
  have H : ∀ p : V, IsBounded p → IsSigma1 p := by
    apply IsBounded.induction 𝚺 (P := fun p ↦ IsSigma1 p);
    · definability;
    · simp;
    · simp;
    · intro k r v; simp;
    · intro k r v; simp;
    · intro p q _ _ ihp ihq; simp [ihp, ihq];
    · intro p q _ _ ihp ihq; simp [ihp, ihq];
    · intro t q ht _ ih;
      exact IsSigma1.mk <| by grind;
    · intro t q _ _ ih;
      simp [qqBex, Arithmetic.qqLT, ih];
  exact H p h;

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

/-! ## Correctness of `IsBounded`: `IsBounded ⌜ψ⌝ ↔ ℬ[<, ℒₒᵣ].Closure ψ` -/

open Bootstrapping in
lemma quote_bex {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) (φ : ArithmeticSemiproposition (n + 1)) :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemiproposition n)⌝ : ℕ)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.bexs_eq];
  simp only [Semiformula.Operator.lt_def, Semiformula.quote_ex,
    Semiformula.quote_and, qqBex, qqExs_inj, qqAnd_inj, and_true];
  simp [Semiformula.quote_rel, Arithmetic.qqLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one];
  rfl;

open Bootstrapping in
lemma isBounded_of_bounded {n : ℕ} {ψ : ArithmeticSemiproposition n}
    (h : ℬ[<, ℒₒᵣ].Closure ψ) : IsBounded (⌜ψ⌝ : ℕ) := by
  revert h;
  apply Bounding.Closure.arithmetic_induction (P := fun n φ ↦ IsBounded (⌜φ⌝ : ℕ));
  · intro n; simp;
  · intro n; simp;
  · intro n t₁ t₂; simp [Semiformula.quote_rel];
  · intro n t₁ t₂; simp [Semiformula.quote_nrel];
  · intro n t₁ t₂; simp [Semiformula.quote_rel];
  · intro n t₁ t₂; simp [Semiformula.quote_nrel];
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_and] using ⟨ihφ, ihψ⟩;
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_or] using ⟨ihφ, ihψ⟩;
  · intro n t φ hφ ihφ;
    rw [quote_ball];
    exact IsBounded.ball (by simp [Semiterm.quote_def]) ihφ;
  · intro n t φ hφ ihφ;
    rw [quote_bex];
    exact IsBounded.bex (by simp [Semiterm.quote_def]) ihφ;

open Bootstrapping in
lemma bounded_of_isBounded {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsBounded (⌜ψ⌝ : ℕ) → ℬ[<, ℒₒᵣ].Closure ψ := by
  induction ψ using Semiformula.rec' with
  | hverum => intro _; simp;
  | hfalsum => intro _; simp;
  | hrel R v => intro _; exact .rel _ _;
  | hnrel R v => intro _; exact .nrel _ _;
  | hand φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_and (V := ℕ) φ ψ, IsBounded.and_iff] at h;
      exact .and (ihφ h.1) (ihψ h.2);
  | hor φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_or (V := ℕ) φ ψ, IsBounded.or_iff] at h;
      exact .or (ihφ h.1) (ihψ h.2);
  | hall φ ihφ =>
      intro h;
      rw [Semiformula.quote_all (V := ℕ) φ] at h;
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, hφeq⟩ := IsBounded.of_all h;
      have hsf := Semiformula.quote_isSemiformula (V := ℕ) φ
      simp only [natCast_nat] at hsf;
      rw [hφeq, Arithmetic.qqNLT] at hsf;
      simp only [IsSemiformula.or, IsSemiformula.nrel] at hsf;
      obtain ⟨⟨_, hvec⟩, hqsf⟩ := hsf;
      obtain ⟨φ₂, hφ₂⟩ := IsSemiformula.sound hqsf;
      have htmsf := hvec.nth (i := 1) (show (1 : ℕ) < 2 by simp)
      simp only [nth_adjoin_one, nth_adjoin_zero] at htmsf;
      obtain ⟨s, hs⟩ := IsSemiterm.sound
        ((IsSemiterm.def (L := ℒₒᵣ)).mpr ⟨ht,
          (termBV_termBShift_le (L := ℒₒᵣ) ht _).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp htmsf).2⟩);
      have heq : (∀¹ φ) = ∀¹[“#0 < !!(Rew.bShift s)”] φ₂ := by
        apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp;
        rw [Semiformula.quote_all (V := ℕ) φ, hφeq, quote_ball, hs, hφ₂];
        rfl;
      have hφ : ℬ[<, ℒₒᵣ].Closure φ :=
        ihφ (by rw [hφeq]; simp [IsBounded.or_iff, hq, Arithmetic.qqNLT])
      have hφ2 : ℬ[<, ℒₒᵣ].Closure φ₂ := by
        have hform : φ = (“#0 < !!(Rew.bShift s)” 🡒 φ₂) :=
          (Semiformula.all_inj _ _).mp (by rw [← Semiformula.ball_eq]; exact heq)
        rw [hform, Semiformula.imp_eq] at hφ;
        exact (Bounding.Closure.or_iff.mp hφ).2;
      rw [heq];
      exact .ball (by rfl) (Rew.positive_iff.mpr ⟨s, rfl⟩) hφ2;
  | hexs φ ihφ =>
      intro h;
      rw [Semiformula.quote_ex (V := ℕ) φ] at h;
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, hφeq⟩ := IsBounded.of_ex h;
      have hsf := Semiformula.quote_isSemiformula (V := ℕ) φ
      simp only [natCast_nat] at hsf;
      rw [hφeq, Arithmetic.qqLT] at hsf;
      simp only [IsSemiformula.and, IsSemiformula.rel] at hsf;
      obtain ⟨⟨_, hvec⟩, hqsf⟩ := hsf;
      obtain ⟨φ₂, hφ₂⟩ := IsSemiformula.sound hqsf;
      have htmsf := hvec.nth (i := 1) (show (1 : ℕ) < 2 by simp)
      simp only [nth_adjoin_one, nth_adjoin_zero] at htmsf;
      obtain ⟨s, hs⟩ := IsSemiterm.sound
        ((IsSemiterm.def (L := ℒₒᵣ)).mpr ⟨ht,
          (termBV_termBShift_le (L := ℒₒᵣ) ht _).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp htmsf).2⟩);
      have heq : (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift s)”] φ₂ := by
        apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp;
        rw [Semiformula.quote_ex (V := ℕ) φ, hφeq, quote_bex, hs, hφ₂];
        rfl;
      have hφ : ℬ[<, ℒₒᵣ].Closure φ :=
        ihφ (by rw [hφeq]; simp [IsBounded.and_iff, hq, Arithmetic.qqLT])
      have hφ2 : ℬ[<, ℒₒᵣ].Closure φ₂ := by
        have hform : φ = (“#0 < !!(Rew.bShift s)” ⋏ φ₂) :=
          (Semiformula.exs_inj _ _).mp (by rw [← Semiformula.bexs_eq]; exact heq)
        rw [hform] at hφ;
        exact (Bounding.Closure.and_iff.mp hφ).2;
      rw [heq];
      exact .bexs (by rfl) (Rew.positive_iff.mpr ⟨s, rfl⟩) hφ2;

lemma isBounded_iff_bounded {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    Bootstrapping.IsBounded (⌜ψ⌝ : ℕ) ↔ ℬ[<, ℒₒᵣ].Closure ψ :=
  ⟨bounded_of_isBounded ψ, isBounded_of_bounded⟩

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping in
lemma isBounded_quote_iff_s {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsBounded (⌜ψ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Closure ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] isBounded.val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] isBounded.val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isBounded)
        (IsBounded.defined (V := ℕ)).proper (IsBounded.defined (V := V)).proper (e := ![⌜ψ⌝])
  by simpa [(IsBounded.defined (V := V)).df, (IsBounded.defined (V := ℕ)).df,
    isBounded_iff_bounded] using h

open Bootstrapping in
lemma isBounded_quote_iff {n : ℕ} (σ : ArithmeticSemisentence n) :
    IsBounded (⌜σ⌝ : V) ↔ ℬ[<, ℒₒᵣ].Closure σ := by
  simp [Sentence.quote_def, isBounded_quote_iff_s];

end FFL.FirstOrder.Arithmetic
