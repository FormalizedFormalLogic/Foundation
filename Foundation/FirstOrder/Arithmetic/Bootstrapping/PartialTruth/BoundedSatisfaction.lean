module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.FamilyRec
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.TermVal

/-!
# Satisfaction for $\Delta_0$ formulas

`boundedSatValue e z` is the truth value of the coded formula `z` under the assignment `e`: `1`
(true) or `0` (false) if `z` is $\Delta_0$, and `2` otherwise. `BoundedSatisfaction z e` says that
this value is `1`.

## References

- [HP98, Lemma I.1.68(2), Theorem I.1.70, Definition I.1.71(2), Lemma I.1.73]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The truth value -/

namespace BoundedSatValue

/-- The term `u` of `(^#0 ^≮ u) ^⋎ q` and of `(^#0 ^< u) ^⋏ q`. -/
noncomputable def boundTerm (p : V) : V := (π₂ (π₂ (π₂ (π₁ (π₂ (p - 1)) - 1)))).[1]

@[simp] lemma boundTerm_ball (u q : V) : boundTerm ((^#0 ^≮ u) ^⋎ q) = u := by
  simp [boundTerm, qqOr, Arithmetic.qqNLT, qqNRel];

@[simp] lemma boundTerm_bex (u q : V) : boundTerm ((^#0 ^< u) ^⋏ q) = u := by
  simp [boundTerm, qqAnd, Arithmetic.qqLT, qqRel];

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma numeral_eqIndex : (ORingStructure.numeral Arithmetic.eqIndex : V) = 0 := rfl

noncomputable def blueprint : UformulaFamilyRec.Blueprint where
  rel := .mkSigma “y e k r v. ∃ t, !nthDef t v 0 ∧ ∃ u, !nthDef u v 1 ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧
    ((r = ↑Arithmetic.eqIndex ∧ a = b ∨ r ≠ ↑Arithmetic.eqIndex ∧ a < b) ∧ y = 1 ∨
      ¬(r = ↑Arithmetic.eqIndex ∧ a = b ∨ r ≠ ↑Arithmetic.eqIndex ∧ a < b) ∧ y = 0)”
  nrel := .mkSigma “y e k r v. ∃ t, !nthDef t v 0 ∧ ∃ u, !nthDef u v 1 ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧
    ((r = ↑Arithmetic.eqIndex ∧ a = b ∨ r ≠ ↑Arithmetic.eqIndex ∧ a < b) ∧ y = 0 ∨
      ¬(r = ↑Arithmetic.eqIndex ∧ a = b ∨ r ≠ ↑Arithmetic.eqIndex ∧ a < b) ∧ y = 1)”
  verum := .mkSigma “y e. y = 1”
  falsum := .mkSigma “y e. y = 0”
  and := .mkSigma “y e p₁ p₂ y₁ y₂.
    (!isBounded.sigma p₁ ∧ !isBounded.sigma p₂ ∧
      (y₁ = 1 ∧ y₂ = 1 ∧ y = 1 ∨ ¬(y₁ = 1 ∧ y₂ = 1) ∧ y = 0)) ∨
    (¬(!isBounded.pi p₁ ∧ !isBounded.pi p₂) ∧ y = 2)”
  or := .mkSigma “y e p₁ p₂ y₁ y₂.
    (!isBounded.sigma p₁ ∧ !isBounded.sigma p₂ ∧
      ((y₁ = 1 ∨ y₂ = 1) ∧ y = 1 ∨ ¬(y₁ = 1 ∨ y₂ = 1) ∧ y = 0)) ∨
    (¬(!isBounded.pi p₁ ∧ !isBounded.pi p₂) ∧ y = 2)”
  all := .mkSigma “y e p ys. ∃ q, !qqAllDef q p ∧ ∃ l, !lenDef l ys ∧
    ((!isBounded.sigma q ∧
      ((∀ i < l, ∃ z, !nthDef z ys i ∧ z = 1) ∧ y = 1 ∨
        (∃ i < l, ∃ z, !nthDef z ys i ∧ z ≠ 1) ∧ y = 0)) ∨
    (¬!isBounded.pi q ∧ y = 2))”
  allSize := .mkSigma “n e p. ∃ p', !subDef p' p 1 ∧ ∃ c, !pi₂Def c p' ∧ ∃ a, !pi₁Def a c ∧
    ∃ a', !subDef a' a 1 ∧ ∃ b, !pi₂Def b a' ∧ ∃ b', !pi₂Def b' b ∧ ∃ w, !pi₂Def w b' ∧
    ∃ u, !nthDef u w 1 ∧ ∃ e', !adjoinDef e' 0 e ∧ !termValGraph n e' u”
  allChanges := .mkSigma “e' e i. !adjoinDef e' i e”
  exs := .mkSigma “y e p ys. ∃ q, !qqExsDef q p ∧ ∃ l, !lenDef l ys ∧
    ((!isBounded.sigma q ∧
      ((∃ i < l, ∃ z, !nthDef z ys i ∧ z = 1) ∧ y = 1 ∨
        (∀ i < l, ∃ z, !nthDef z ys i ∧ z ≠ 1) ∧ y = 0)) ∨
    (¬!isBounded.pi q ∧ y = 2))”
  exsSize := .mkSigma “n e p. ∃ p', !subDef p' p 1 ∧ ∃ c, !pi₂Def c p' ∧ ∃ a, !pi₁Def a c ∧
    ∃ a', !subDef a' a 1 ∧ ∃ b, !pi₂Def b a' ∧ ∃ b', !pi₂Def b' b ∧ ∃ w, !pi₂Def w b' ∧
    ∃ u, !nthDef u w 1 ∧ ∃ e', !adjoinDef e' 0 e ∧ !termValGraph n e' u”
  exsChanges := .mkSigma “e' e i. !adjoinDef e' i e”

open Classical in
noncomputable def construction : UformulaFamilyRec.Construction V blueprint where
  rel e _ r v := if r = Arithmetic.eqIndex ∧ termVal e v.[0] = termVal e v.[1] ∨
    r ≠ Arithmetic.eqIndex ∧ termVal e v.[0] < termVal e v.[1] then 1 else 0
  rel_defined := .mk fun v ↦ by
    simp [blueprint, (termVal.defined (V := V)).df, numeral_eqIndex];
    grind;
  nrel e _ r v := if r = Arithmetic.eqIndex ∧ termVal e v.[0] = termVal e v.[1] ∨
    r ≠ Arithmetic.eqIndex ∧ termVal e v.[0] < termVal e v.[1] then 0 else 1
  nrel_defined := .mk fun v ↦ by
    simp [blueprint, (termVal.defined (V := V)).df, numeral_eqIndex];
    grind;
  verum _ := 1
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum _ := 0
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and _ p₁ p₂ y₁ y₂ := if IsBounded p₁ ∧ IsBounded p₂ then (if y₁ = 1 ∧ y₂ = 1 then 1 else 0) else 2
  and_defined := .mk fun v ↦ by
    simp [blueprint, HierarchySymbol.Semiformula.val_sigma, IsBounded.defined.df,
      IsBounded.defined.proper.iff'];
    grind;
  or _ p₁ p₂ y₁ y₂ := if IsBounded p₁ ∧ IsBounded p₂ then (if y₁ = 1 ∨ y₂ = 1 then 1 else 0) else 2
  or_defined := .mk fun v ↦ by
    simp [blueprint, HierarchySymbol.Semiformula.val_sigma, IsBounded.defined.df,
      IsBounded.defined.proper.iff'];
    grind;
  all _ p ys := if IsBounded (^∀ p) then (if ∀ i < len ys, ys.[i] = 1 then 1 else 0) else 2
  all_defined := .mk fun v ↦ by
    simp [blueprint, HierarchySymbol.Semiformula.val_sigma, IsBounded.defined.df,
      IsBounded.defined.proper.iff'];
    grind;
  allSize e p := termVal (0 ∷ e) (boundTerm p)
  allSize_defined := .mk fun v ↦ by simp [blueprint, boundTerm, (termVal.defined (V := V)).df]
  allChanges e i := i ∷ e
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_monotone h := adjoin_le_adjoin h le_rfl
  exs _ p ys := if IsBounded (^∃ p) then (if ∃ i < len ys, ys.[i] = 1 then 1 else 0) else 2
  exs_defined := .mk fun v ↦ by
    simp [blueprint, HierarchySymbol.Semiformula.val_sigma, IsBounded.defined.df,
      IsBounded.defined.proper.iff'];
    split_ifs <;> simp_all;
  exsSize e p := termVal (0 ∷ e) (boundTerm p)
  exsSize_defined := .mk fun v ↦ by simp [blueprint, boundTerm, (termVal.defined (V := V)).df]
  exsChanges e i := i ∷ e
  exsChanges_defined := .mk fun v ↦ by simp [blueprint]
  exsChanges_monotone h := adjoin_le_adjoin h le_rfl

end BoundedSatValue

open BoundedSatValue

noncomputable def boundedSatValue (e z : V) : V := construction.result ℒₒᵣ e z

noncomputable def boundedSatValueGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.result ℒₒᵣ

instance boundedSatValue.defined :
    𝚺ᴬ₁-Function₂ (boundedSatValue : V → V → V) via boundedSatValueGraph :=
  construction.result_defined

instance boundedSatValue.definable : 𝚺ᴬ₁-Function₂ (boundedSatValue : V → V → V) :=
  boundedSatValue.defined.to_definable

section value

variable {e t u p q : V}

@[simp] lemma boundedSatValue_verum : boundedSatValue e (^⊤ : V) = 1 := by
  simp [boundedSatValue, construction];

@[simp] lemma boundedSatValue_falsum : boundedSatValue e (^⊥ : V) = 0 := by
  simp [boundedSatValue, construction];

section
variable (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

open Classical in
@[simp] lemma boundedSatValue_eq :
    boundedSatValue e (t ^= u) = if termVal e t = termVal e u then 1 else 0 := by
  simp [boundedSatValue, construction, Arithmetic.qqEQ, ht, hu];

open Classical in
@[simp] lemma boundedSatValue_neq :
    boundedSatValue e (t ^≠ u) = if termVal e t = termVal e u then 0 else 1 := by
  simp [boundedSatValue, construction, Arithmetic.qqNEQ, ht, hu];

open Classical in
@[simp] lemma boundedSatValue_lt :
    boundedSatValue e (t ^< u) = if termVal e t < termVal e u then 1 else 0 := by
  simp [boundedSatValue, construction, Arithmetic.qqLT, ht, hu];

open Classical in
@[simp] lemma boundedSatValue_nlt :
    boundedSatValue e (t ^≮ u) = if termVal e t < termVal e u then 0 else 1 := by
  simp [boundedSatValue, construction, Arithmetic.qqNLT, ht, hu];

end

section
variable (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
include hp hq

open Classical in
@[simp] lemma boundedSatValue_and :
    boundedSatValue e (p ^⋏ q) = if IsBounded p ∧ IsBounded q then
      (if boundedSatValue e p = 1 ∧ boundedSatValue e q = 1 then 1 else 0) else 2 := by
  rw [boundedSatValue, UformulaFamilyRec.Construction.result_and hp hq]; rfl;

open Classical in
@[simp] lemma boundedSatValue_or :
    boundedSatValue e (p ^⋎ q) = if IsBounded p ∧ IsBounded q then
      (if boundedSatValue e p = 1 ∨ boundedSatValue e q = 1 then 1 else 0) else 2 := by
  rw [boundedSatValue, UformulaFamilyRec.Construction.result_or hp hq]; rfl;

end

open Classical in
lemma boundedSatValue_all (hp : IsUFormula ℒₒᵣ p) :
    boundedSatValue e (^∀ p) = if IsBounded (^∀ p) then
      (if ∀ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 then 1 else 0)
      else 2 := by
  obtain ⟨ys, ⟨hl, hys⟩, h⟩ := construction.result_all (param := e) hp;
  have H : (∀ i < len ys, ys.[i] = 1) ↔
      ∀ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 := by
    rw [hl]; exact forall₂_congr fun i hi ↦ by rw [hys i hi]; rfl;
  rw [boundedSatValue, h];
  exact if_congr Iff.rfl (if_congr H rfl rfl) rfl;

open Classical in
lemma boundedSatValue_exs (hp : IsUFormula ℒₒᵣ p) :
    boundedSatValue e (^∃ p) = if IsBounded (^∃ p) then
      (if ∃ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 then 1 else 0)
      else 2 := by
  obtain ⟨ys, ⟨hl, hys⟩, h⟩ := construction.result_exs (param := e) hp;
  have H : (∃ i < len ys, ys.[i] = 1) ↔
      ∃ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 := by
    rw [hl]; exact exists_congr fun i ↦ and_congr_right fun hi ↦ by rw [hys i hi]; rfl;
  rw [boundedSatValue, h];
  exact if_congr Iff.rfl (if_congr H rfl rfl) rfl;

section
variable (ht : IsUTerm ℒₒᵣ t) (hq : IsUFormula ℒₒᵣ q)
include ht hq

open Classical in
@[simp] lemma boundedSatValue_ball :
    boundedSatValue e (qqBall (termBShift ℒₒᵣ t) q) = if IsBounded q then
      (if ∀ x < termVal e t, boundedSatValue (x ∷ e) q = 1 then 1 else 0) else 2 := by
  have hb : IsBounded (qqBall (termBShift ℒₒᵣ t) q) ↔ IsBounded q :=
    ⟨IsBounded.of_qqBall, IsBounded.ball ht⟩;
  have hg : IsUFormula ℒₒᵣ (^#0 ^≮ termBShift ℒₒᵣ t) := by simp [Arithmetic.qqNLT, ht.termBShift];
  rw [qqBall] at hb ⊢;
  rw [boundedSatValue_all (by simp [hg, hq]), hb, boundTerm_ball, termVal_termBShift ht];
  by_cases hbq : IsBounded q;
  · have H : (∀ x < termVal e t,
        boundedSatValue (x ∷ e) ((^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) = 1) ↔
        ∀ x < termVal e t, boundedSatValue (x ∷ e) q = 1 :=
      forall₂_congr fun x hx ↦ by
        simp [ht.termBShift, hg, hq, hbq, termVal_termBShift ht, hx,
          show IsBounded (^#0 ^≮ termBShift ℒₒᵣ t) by simp [Arithmetic.qqNLT]];
    exact if_congr Iff.rfl (if_congr H rfl rfl) rfl;
  · simp [hbq];

open Classical in
@[simp] lemma boundedSatValue_bex :
    boundedSatValue e (qqBex (termBShift ℒₒᵣ t) q) = if IsBounded q then
      (if ∃ x < termVal e t, boundedSatValue (x ∷ e) q = 1 then 1 else 0) else 2 := by
  have hb : IsBounded (qqBex (termBShift ℒₒᵣ t) q) ↔ IsBounded q :=
    ⟨IsBounded.of_qqBex, IsBounded.bex ht⟩;
  have hg : IsUFormula ℒₒᵣ (^#0 ^< termBShift ℒₒᵣ t) := by simp [Arithmetic.qqLT, ht.termBShift];
  rw [qqBex] at hb ⊢;
  rw [boundedSatValue_exs (by simp [hg, hq]), hb, boundTerm_bex, termVal_termBShift ht];
  by_cases hbq : IsBounded q;
  · have H : (∃ x < termVal e t,
        boundedSatValue (x ∷ e) ((^#0 ^< termBShift ℒₒᵣ t) ^⋏ q) = 1) ↔
        ∃ x < termVal e t, boundedSatValue (x ∷ e) q = 1 :=
      exists_congr fun x ↦ and_congr_right fun hx ↦ by
        simp [ht.termBShift, hg, hq, hbq, termVal_termBShift ht, hx,
          show IsBounded (^#0 ^< termBShift ℒₒᵣ t) by simp [Arithmetic.qqLT]];
    exact if_congr Iff.rfl (if_congr H rfl rfl) rfl;
  · simp [hbq];

end

end value

/-! ## The satisfaction predicate -/

def BoundedSatisfaction (z e : V) : Prop := boundedSatValue e z = 1

noncomputable def boundedSatisfaction : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “z e. ∃ y, !boundedSatValueGraph y e z ∧ y = 1”)
  (.mkPi “z e. ∀ y, !boundedSatValueGraph y e z → y = 1”)

instance BoundedSatisfaction.defined :
    𝚫ᴬ₁-Relation (BoundedSatisfaction : V → V → Prop) via boundedSatisfaction := .mk <| by
  constructor;
  · intro v; simp [boundedSatisfaction, boundedSatValue.defined.iff];
  · intro v; simp [boundedSatisfaction, BoundedSatisfaction, boundedSatValue.defined.iff];

instance BoundedSatisfaction.definable : 𝚫ᴬ₁-Relation (BoundedSatisfaction : V → V → Prop) :=
  BoundedSatisfaction.defined.to_definable

namespace BoundedSatisfaction

lemma dom {z e : V} (h : BoundedSatisfaction z e) : IsBounded z ∧ IsUFormula ℒₒᵣ z := by
  by_cases hz : IsUFormula ℒₒᵣ z;
  · suffices IsBounded z from ⟨this, hz⟩;
    by_contra hb;
    rcases hz.case with (⟨k, r, v, -, -, rfl⟩ | ⟨k, r, v, -, -, rfl⟩ | rfl | rfl |
      ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩) <;>
      simp_all [BoundedSatisfaction, boundedSatValue_all, boundedSatValue_exs, ite_eq_iff];
  · simp [BoundedSatisfaction, boundedSatValue,
      UformulaFamilyRec.Construction.result_prop_not _ hz] at h;

@[simp] lemma verum (e : V) : BoundedSatisfaction (^⊤ : V) e := by simp [BoundedSatisfaction]

@[simp] lemma falsum (e : V) : ¬BoundedSatisfaction (^⊥ : V) e := by simp [BoundedSatisfaction]

section
variable {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

@[simp] lemma eq_iff : BoundedSatisfaction (t ^= u) e ↔ termVal e t = termVal e u := by
  simp [BoundedSatisfaction, ht, hu];

@[simp] lemma neq_iff : BoundedSatisfaction (t ^≠ u) e ↔ termVal e t ≠ termVal e u := by
  simp [BoundedSatisfaction, ht, hu];

@[simp] lemma lt_iff : BoundedSatisfaction (t ^< u) e ↔ termVal e t < termVal e u := by
  simp [BoundedSatisfaction, ht, hu];

@[simp] lemma nlt_iff : BoundedSatisfaction (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := by
  simp [BoundedSatisfaction, ht, hu];

end

@[simp] lemma and_iff {p q e : V} :
    BoundedSatisfaction (p ^⋏ q) e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e := by
  constructor;
  · intro h; have := h.dom; simp_all [BoundedSatisfaction];
  · rintro ⟨h₁, h₂⟩; have := h₁.dom; have := h₂.dom; simp_all [BoundedSatisfaction];

@[simp] lemma or_iff {p q e : V} (hdp : IsBounded p) (hfp : IsUFormula ℒₒᵣ p)
    (hdq : IsBounded q) (hfq : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (p ^⋎ q) e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e := by
  simp [BoundedSatisfaction, hdp, hfp, hdq, hfq, or_iff_not_imp_left];

section
variable {t q e : V} (ht : IsUTerm ℒₒᵣ t)
include ht

@[simp] lemma ball_iff (hq : IsBounded q) (hq' : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (qqBall (termBShift ℒₒᵣ t) q) e ↔
      ∀ x < termVal e t, BoundedSatisfaction q (x ∷ e) := by
  simp [BoundedSatisfaction, ht, hq, hq'];

@[simp] lemma bex_iff :
    BoundedSatisfaction (qqBex (termBShift ℒₒᵣ t) q) e ↔
      ∃ x < termVal e t, BoundedSatisfaction q (x ∷ e) := by
  by_cases h : IsBounded q ∧ IsUFormula ℒₒᵣ q;
  · simp [BoundedSatisfaction, ht, h.1, h.2];
  · apply iff_of_false;
    · intro hs;
      exact h ⟨hs.dom.1.of_qqBex,
        by simpa [qqBex, Arithmetic.qqLT, ht.termBShift] using hs.dom.2⟩;
    · exact fun ⟨_, _, hs⟩ ↦ h hs.dom;

end

lemma neg_iff {p e : V} (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e := by
  have H : ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p →
      ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ IsUFormula ℒₒᵣ p →
        ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e));
    · definability;
    · intro _ e; simp;
    · intro _ e; simp;
    · intro k r v h e;
      rcases Arithmetic.rel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq, Arithmetic.neg_eq ht hu, neq_iff ht hu, eq_iff ht hu];
      · rw [heq, Arithmetic.neg_lt ht hu, nlt_iff ht hu, lt_iff ht hu];
    · intro k r v h e;
      rcases Arithmetic.nrel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq, Arithmetic.neg_neq ht hu, eq_iff ht hu, neq_iff ht hu]; simp;
      · rw [heq, Arithmetic.neg_nlt ht hu, lt_iff ht hu, nlt_iff ht hu]; simp;
    · intro p q hdp hdq ihp ihq h e;
      obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp h;
      rw [neg_and hfp hfq, or_iff (IsBounded.neg hfp hdp) hfp.neg (IsBounded.neg hfq hdq) hfq.neg,
        ihp hfp e, ihq hfq e, and_iff];
      tauto;
    · intro p q hdp hdq ihp ihq h e;
      obtain ⟨hfp, hfq⟩ := IsUFormula.or.mp h;
      rw [neg_or hfp hfq, and_iff, ihp hfp e, ihq hfq e, or_iff hdp hfp hdq hfq];
      tauto;
    · intro t q ht hdq ih h e;
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h;
      rw [neg_qqBall ht.termBShift hfq, bex_iff ht, ball_iff ht hdq hfq];
      simp [ih hfq];
    · intro t q ht hdq ih h e;
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h;
      rw [neg_qqBex ht.termBShift hfq, ball_iff ht (IsBounded.neg hfq hdq) hfq.neg, bex_iff ht];
      simp [ih hfq];
  exact H p hp hp' e;

section
variable {n m w k r v e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
include hw

lemma subst_rel (hp : IsSemiformula ℒₒᵣ n (^rel k r v)) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w (^rel k r v)) e ↔
      BoundedSatisfaction (^rel k r v) (termValVec e n w) := by
  rcases Arithmetic.rel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢;
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqEQ] using hp;
    rw [Arithmetic.substs_eq ht hu, eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      eq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqLT] using hp;
    rw [Arithmetic.substs_lt ht hu, lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      lt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];

lemma subst_nrel (hp : IsSemiformula ℒₒᵣ n (^nrel k r v)) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w (^nrel k r v)) e ↔
      BoundedSatisfaction (^nrel k r v) (termValVec e n w) := by
  rcases Arithmetic.nrel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢;
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqNEQ] using hp;
    rw [Arithmetic.substs_neq ht hu, neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      neq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqNLT] using hp;
    rw [Arithmetic.substs_nlt ht hu, nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      nlt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];

end

lemma subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsBounded p) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
      BoundedSatisfaction p (termValVec e n w) := by
  have H : ∀ p : V, IsBounded p → ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
        BoundedSatisfaction p (termValVec e n w)) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
          BoundedSatisfaction p (termValVec e n w)));
    · definability;
    · intro n m w e _ _; simp;
    · intro n m w e _ _; simp;
    · intro k r v n m w e hw hp;
      exact subst_rel hw hp;
    · intro k r v n m w e hw hp;
      exact subst_nrel hw hp;
    · intro p q _ _ ihp ihq n m w e hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq;
      rw [substs_and hp.isUFormula hq.isUFormula, and_iff, and_iff, ihp n m w e hw hp,
        ihq n m w e hw hq];
    · intro p q hdp hdq ihp ihq n m w e hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq;
      rw [substs_or hp.isUFormula hq.isUFormula,
        or_iff (IsBounded.subst hw hp hdp) (hp.subst hw).isUFormula
          (IsBounded.subst hw hq hdq) (hq.subst hw).isUFormula,
        or_iff hdp hp.isUFormula hdq hq.isUFormula,
        ihp n m w e hw hp, ihq n m w e hw hq];
    · intro t q ht hdq ih n m w e hw hpq;
      obtain ⟨hts, hq⟩ := isSemiformula_qqBall ht hpq;
      rw [substs_qqBall hw hts hq.isUFormula,
        ball_iff (hw.termSubst hts).isUTerm (IsBounded.subst hw.qVec hq hdq)
          (hq.subst hw.qVec).isUFormula,
        ball_iff ht hdq hq.isUFormula, termVal_termSubst hw hts];
      exact forall₂_congr fun x _ ↦ by
        rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
    · intro t q ht hdq ih n m w e hw hpq;
      obtain ⟨hts, hq⟩ := isSemiformula_qqBex ht hpq;
      rw [substs_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm, bex_iff ht,
        termVal_termSubst hw hts];
      exact exists_congr fun x ↦ and_congr_right fun _ ↦ by
        rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
  exact H p hp' n m w e hw hp;

end BoundedSatisfaction

theorem boundedSatisfaction_quote_iff {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) (v : Fin k → V) :
    BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  revert hφ v;
  apply Bounding.Closure.arithmetic_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ v : Fin k → V, BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ);
  · intro n v; simp [Sentence.quote_verum];
  · intro n v; simp [Sentence.quote_falsum];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_rel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_nrel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_rel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_nrel];
  · intro n φ ψ hφ hψ ihφ ihψ v; simp [ihφ v, ihψ v];
  · intro n φ ψ hφ hψ ihφ ihψ v; simp [isBounded_quote_iff, hφ, hψ, ihφ v, ihψ v];
  · intro n t φ hφ ihφ v;
    rw [quote_ball_sentence, BoundedSatisfaction.ball_iff (by simp) ((isBounded_quote_iff φ).mpr hφ)
      (by simp), termVal_quote];
    simp [← ihφ, Function.comp_def];
  · intro n t φ hφ ihφ v;
    rw [quote_bex_sentence, BoundedSatisfaction.bex_iff (by simp), termVal_quote];
    simp [← ihφ, Function.comp_def];

end FFL.FirstOrder.Arithmetic.Bootstrapping
