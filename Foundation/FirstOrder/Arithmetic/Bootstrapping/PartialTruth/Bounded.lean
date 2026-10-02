module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.TermVal

/-!
# Satisfaction and truth for $\Delta_0$ formulas

`boundedSatValue e z` is the truth value of the coded formula `z` under the assignment `e`: `1`
(true) or `0` (false) if `z` is $\Delta_0$, and `2` otherwise. `BoundedSatisfaction z e` says that
this value is `1`, and `BoundedTruth` is the truth predicate for the codes of $\Delta_0$ sentences.

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

noncomputable def blueprint : UformulaRec1.Blueprint where
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
noncomputable def construction : UformulaRec1.Construction V blueprint where
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
  exChanges_defined := .mk fun v ↦ by simp [blueprint]
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
  rw [boundedSatValue, construction.result_and hp hq]; rfl;

open Classical in
@[simp] lemma boundedSatValue_or :
    boundedSatValue e (p ^⋎ q) = if IsBounded p ∧ IsBounded q then
      (if boundedSatValue e p = 1 ∨ boundedSatValue e q = 1 then 1 else 0) else 2 := by
  rw [boundedSatValue, construction.result_or hp hq]; rfl;

end

open Classical in
lemma boundedSatValue_all (hp : IsUFormula ℒₒᵣ p) :
    boundedSatValue e (^∀ p) = if IsBounded (^∀ p) then
      (if ∀ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 then 1 else 0)
      else 2 := by
  obtain ⟨ys, ⟨hl, hys⟩, h⟩ :=
    construction.graph_all_inv (construction.result_prop e (by simpa using hp));
  have H : (∀ i < len ys, ys.[i] = 1) ↔
      ∀ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 := by
    rw [hl];
    exact forall₂_congr fun i hi ↦ by rw [← construction.result_eq_of_graph (hys i hi)]; rfl;
  rw [boundedSatValue, h];
  exact if_congr Iff.rfl (if_congr H rfl rfl) rfl;

open Classical in
lemma boundedSatValue_exs (hp : IsUFormula ℒₒᵣ p) :
    boundedSatValue e (^∃ p) = if IsBounded (^∃ p) then
      (if ∃ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 then 1 else 0)
      else 2 := by
  obtain ⟨ys, ⟨hl, hys⟩, h⟩ :=
    construction.graph_ex_inv (construction.result_prop e (by simpa using hp));
  have H : (∃ i < len ys, ys.[i] = 1) ↔
      ∃ x < termVal (0 ∷ e) (boundTerm p), boundedSatValue (x ∷ e) p = 1 := by
    rw [hl];
    exact exists_congr fun i ↦ and_congr_right fun hi ↦ by
      rw [← construction.result_eq_of_graph (hys i hi)]; rfl;
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
      construction.result_prop_not _ hz] at h;

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

/-! ## The truth predicate -/

def BoundedTruth (x : V) : Prop := BoundedSatisfaction x 0

noncomputable def boundedTruth : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. !boundedSatisfaction.sigma x 0”)
  (.mkPi “x. !boundedSatisfaction.pi x 0”)

instance BoundedTruth.defined :
    𝚫ᴬ₁-Predicate (BoundedTruth : V → Prop) via boundedTruth := .mk <| by
  constructor;
  · intro v; simp [boundedTruth, BoundedSatisfaction.defined.proper.iff'];
  · intro v; simp [boundedTruth, BoundedTruth];

instance BoundedTruth.definable : 𝚫ᴬ₁-Predicate (BoundedTruth : V → Prop) :=
  BoundedTruth.defined.to_definable

theorem boundedTruth_quote_iff {σ : ArithmeticSentence} (hσ : ℬ[<, ℒₒᵣ].Closure σ) :
    BoundedTruth (⌜σ⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ σ := by
  simpa [BoundedTruth, matrixToVec_nil, models_iff] using
    boundedSatisfaction_quote_iff (V := V) hσ ![]

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_boundedTruth_iff
    {σ : ArithmeticSentence} (hσ : ℬ[<, ℒₒᵣ].Closure σ) :
    𝗜𝚺₁ ⊢ boundedTruth.val/[⌜σ⌝] 🡘 σ :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff, BoundedTruth.defined.df] using boundedTruth_quote_iff hσ

end FFL.FirstOrder.Arithmetic.Bootstrapping
