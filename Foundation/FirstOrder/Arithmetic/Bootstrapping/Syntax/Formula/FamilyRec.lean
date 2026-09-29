module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Basic

/-!
# Recursion on formulas with families of values at quantifiers

`UformulaFamilyRec` is the variant of `UformulaRec1` in which the value at `^∀ p` is computed from
the vector of the values of `p` at the parameters `allChanges param i`, `i < allSize param p`, and
likewise at `^∃ p` with `exsChanges` and `exsSize`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace UformulaFamilyRec

structure Blueprint where
  rel : 𝚺ᴬ₁.Semisentence 5
  nrel : 𝚺ᴬ₁.Semisentence 5
  verum : 𝚺ᴬ₁.Semisentence 2
  falsum : 𝚺ᴬ₁.Semisentence 2
  and : 𝚺ᴬ₁.Semisentence 6
  or : 𝚺ᴬ₁.Semisentence 6
  all : 𝚺ᴬ₁.Semisentence 4
  allSize : 𝚺ᴬ₁.Semisentence 3
  allChanges : 𝚺ᴬ₁.Semisentence 3
  exs : 𝚺ᴬ₁.Semisentence 4
  exsSize : 𝚺ᴬ₁.Semisentence 3
  exsChanges : 𝚺ᴬ₁.Semisentence 3

namespace Blueprint

variable (L) (β : Blueprint)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !(isUFormula L).sigma p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum y param) ∨
    (!qqFalsumDef p ∧ !β.falsum y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧
        !β.and y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧
        !β.or y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ n, !β.allSize n param p₁ ∧ ∃ rv, !repeatVecDef rv C n ∧ ∃ ys <⁺ rv,
      (!lenDef n ys ∧ ∀ i < n, ∃ yi, !nthDef yi ys i ∧
        ∃ param', !β.allChanges param' param i ∧ :⟪param', p₁, yi⟫:∈ C) ∧
      !qqAllDef p p₁ ∧ !β.all y param p₁ ys) ∨
    (∃ p₁ < p, ∃ n, !β.exsSize n param p₁ ∧ ∃ rv, !repeatVecDef rv C n ∧ ∃ ys <⁺ rv,
      (!lenDef n ys ∧ ∀ i < n, ∃ yi, !nthDef yi ys i ∧
        ∃ param', !β.exsChanges param' param i ∧ :⟪param', p₁, yi⟫:∈ C) ∧
      !qqExsDef p p₁ ∧ !β.exs y param p₁ ys))”)
  (.mkPi “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !(isUFormula L).pi p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel.graphDelta.pi.val y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel.graphDelta.pi.val y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum.graphDelta.pi.val y param) ∨
    (!qqFalsumDef p ∧ !β.falsum.graphDelta.pi.val y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧
        !β.and.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧
        !β.or.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∀ n, !β.allSize n param p₁ → ∀ rv, !repeatVecDef rv C n → ∃ ys <⁺ rv,
      ((∀ l, !lenDef l ys → n = l) ∧ ∀ i < n, ∀ yi, !nthDef yi ys i →
        ∀ param', !β.allChanges param' param i → :⟪param', p₁, yi⟫:∈ C) ∧
      !qqAllDef p p₁ ∧ !β.all.graphDelta.pi.val y param p₁ ys) ∨
    (∃ p₁ < p, ∀ n, !β.exsSize n param p₁ → ∀ rv, !repeatVecDef rv C n → ∃ ys <⁺ rv,
      ((∀ l, !lenDef l ys → n = l) ∧ ∀ i < n, ∀ yi, !nthDef yi ys i →
        ∀ param', !β.exsChanges param' param i → :⟪param', p₁, yi⟫:∈ C) ∧
      !qqExsDef p p₁ ∧ !β.exs.graphDelta.pi.val y param p₁ ys))”)⟩

noncomputable def graph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param p y. ∃ pr, !pair₃Def pr param p y ∧ !(β.blueprint L).fixpointDef pr”

noncomputable def result : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y param p. (!(isUFormula L).pi p → !(β.graph L) param p y) ∧ (¬!(isUFormula L).sigma p → y = 0)”

end Blueprint

variable (V)

structure Construction (φ : Blueprint) where
  rel (param k R v : V) : V
  nrel (param k R v : V) : V
  verum (param : V) : V
  falsum (param : V) : V
  and (param p₁ p₂ y₁ y₂ : V) : V
  or (param p₁ p₂ y₁ y₂ : V) : V
  all (param p₁ ys : V) : V
  allSize (param p₁ : V) : V
  allChanges (param i : V) : V
  exs (param p₁ ys : V) : V
  exsSize (param p₁ : V) : V
  exsChanges (param i : V) : V
  rel_defined : 𝚺ᴬ₁-Function₄ rel via φ.rel
  nrel_defined : 𝚺ᴬ₁-Function₄ nrel via φ.nrel
  verum_defined : 𝚺ᴬ₁-Function₁ verum via φ.verum
  falsum_defined : 𝚺ᴬ₁-Function₁ falsum via φ.falsum
  and_defined : 𝚺ᴬ₁-Function₅ and via φ.and
  or_defined : 𝚺ᴬ₁-Function₅ or via φ.or
  all_defined : 𝚺ᴬ₁-Function₃ all via φ.all
  allSize_defined : 𝚺ᴬ₁-Function₂ allSize via φ.allSize
  allChanges_defined : 𝚺ᴬ₁-Function₂ allChanges via φ.allChanges
  exs_defined : 𝚺ᴬ₁-Function₃ exs via φ.exs
  exsSize_defined : 𝚺ᴬ₁-Function₂ exsSize via φ.exsSize
  exsChanges_defined : 𝚺ᴬ₁-Function₂ exsChanges via φ.exsChanges
  allChanges_monotone {param i j : V} : i ≤ j → allChanges param i ≤ allChanges param j
  exsChanges_monotone {param i j : V} : i ≤ j → exsChanges param i ≤ exsChanges param j

variable {V}

namespace Construction

variable (L) {β : Blueprint} (c : Construction V β)

def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧ IsUFormula L p ∧ (
  (∃ k r v, p = ^rel k r v ∧ y = c.rel param k r v) ∨
  (∃ k r v, p = ^nrel k r v ∧ y = c.nrel param k r v) ∨
  (p = ^⊤ ∧ y = c.verum param) ∨
  (p = ^⊥ ∧ y = c.falsum param) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧
    y = c.and param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧
    y = c.or param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ ys, (len ys = c.allSize param p₁ ∧
      ∀ i < c.allSize param p₁, ⟪c.allChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
    p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
  (∃ p₁ ys, (len ys = c.exsSize param p₁ ∧
      ∀ i < c.exsSize param p₁, ⟪c.exsChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
    p = ^∃ p₁ ∧ y = c.exs param p₁ ys))

private lemma phi_iff (C pr : V) :
    c.Phi L {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ IsUFormula L p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ ys ≤ repeatVec C (c.allSize param p₁), (c.allSize param p₁ = len ys ∧
        ∀ i < c.allSize param p₁, ⟪c.allChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
      p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
    (∃ p₁ < p, ∃ ys ≤ repeatVec C (c.exsSize param p₁), (c.exsSize param p₁ = len ys ∧
        ∀ i < c.exsSize param p₁, ⟪c.exsChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
      p = ^∃ p₁ ∧ y = c.exs param p₁ ys)) := by
  have hrv {g : V → V} {p₁ ys n : V} (hl : len ys = n) (hys : ∀ i < n, ⟪g i, p₁, ys.[i]⟫ ∈ C) :
      ys ≤ repeatVec C n := by
    subst hl;
    exact len_repeatVec_of_nth_le fun i hi ↦ le_of_lt <|
      lt_of_le_of_lt ((le_pair_right _ _).trans (le_pair_right _ _)) (lt_of_mem (hys i hi));
  constructor;
  · rintro ⟨param, p, y, rfl, hp, H⟩;
    refine ⟨param, by simp,
      p, le_trans (le_pair_left p y) (le_pair_right _ _),
      y, le_trans (le_pair_right p y) (le_pair_right _ _), rfl, hp, ?_⟩;
    rcases H with (⟨k, r, v, rfl, rfl⟩ | ⟨k, r, v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩);
    · disj 1; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩;
    · disj 2; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩;
    · disj 3; exact ⟨rfl, rfl⟩;
    · disj 4; exact ⟨rfl, rfl⟩;
    · disj 5; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁),
        y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂), h₁, h₂, rfl, rfl⟩;
    · disj 6; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁),
        y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂), h₁, h₂, rfl, rfl⟩;
    · disj 7; exact ⟨p₁, by simp, ys, hrv hl hys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
    · disj 8; exact ⟨p₁, by simp, ys, hrv hl hys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
  · rintro ⟨param, _, p, _, y, _, rfl, hp, H⟩;
    refine ⟨param, p, y, rfl, hp, ?_⟩;
    rcases H with (⟨k, _, r, _, v, _, rfl, rfl⟩ | ⟨k, _, r, _, v, _, rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, ys, _, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, _, ys, _, ⟨hl, hys⟩, rfl, rfl⟩);
    · disj 1; exact ⟨k, r, v, rfl, rfl⟩;
    · disj 2; exact ⟨k, r, v, rfl, rfl⟩;
    · disj 3; exact ⟨rfl, rfl⟩;
    · disj 4; exact ⟨rfl, rfl⟩;
    · disj 5; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩;
    · disj 6; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩;
    · disj 7; exact ⟨p₁, ys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
    · disj 8; exact ⟨p₁, ys, ⟨hl.symm, hys⟩, rfl, rfl⟩;

def construction : Fixpoint.Construction V (β.blueprint L) where
  Φ := fun _ ↦ c.Phi L
  defined := .mk <| by
    constructor;
    · intro v;
      simp [Blueprint.blueprint,
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.allSize_defined.iff, c.allChanges_defined.iff,
        c.exs_defined.iff, c.exs_defined.graph_delta.proper.iff',
        c.exsSize_defined.iff, c.exsChanges_defined.iff];
    · intro v;
      symm;
      simpa [Blueprint.blueprint, c.rel_defined.iff, c.nrel_defined.iff, c.verum_defined.iff,
        c.falsum_defined.iff, c.and_defined.iff, c.or_defined.iff, c.all_defined.iff,
        c.allSize_defined.iff, c.allChanges_defined.iff, c.exs_defined.iff,
        c.exsSize_defined.iff, c.exsChanges_defined.iff] using c.phi_iff L _ _;
  monotone := by
    unfold Phi;
    rintro C C' hC _ _ ⟨param, p, y, rfl, hp, H⟩;
    refine ⟨param, p, y, rfl, hp, ?_⟩;
    rcases H with (h | h | h | h | ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩);
    · disj 1; exact h;
    · disj 2; exact h;
    · disj 3; exact h;
    · disj 4; exact h;
    · disj 5; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩;
    · disj 6; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩;
    · disj 7; exact ⟨p₁, ys, ⟨hl, fun i hi ↦ hC (hys i hi)⟩, rfl, rfl⟩;
    · disj 8; exact ⟨p₁, ys, ⟨hl, fun i hi ↦ hC (hys i hi)⟩, rfl, rfl⟩;

instance : (c.construction L).Finite where
  finite {C _ pr h} := by
    have hlt {a b p₁ ys i : V} (h : a ≤ b) : ⟪a, p₁, ys.[i]⟫ < ⟪b, p₁, ys⟫ + 1 :=
      lt_succ_iff_le.mpr <| pair_le_pair h <| pair_le_pair le_rfl (by simp);
    rcases h with ⟨param, p, y, rfl, hp, (h | h | h | h |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)⟩;
    · exact ⟨0, param, _, _, rfl, hp, by disj 1; exact h⟩;
    · exact ⟨0, param, _, _, rfl, hp, by disj 2; exact h⟩;
    · exact ⟨0, param, _, _, rfl, hp, by disj 3; exact h⟩;
    · exact ⟨0, param, _, _, rfl, hp, by disj 4; exact h⟩;
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        disj 5;
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl,
          rfl⟩⟩;
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        disj 6;
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl,
          rfl⟩⟩;
    · exact ⟨_, param, _, _, rfl, hp, by
        disj 7;
        exact ⟨p₁, ys, ⟨hl, fun i hi ↦ ⟨hys i hi, hlt (c.allChanges_monotone hi.le)⟩⟩, rfl, rfl⟩⟩;
    · exact ⟨_, param, _, _, rfl, hp, by
        disj 8;
        exact ⟨p₁, ys, ⟨hl, fun i hi ↦ ⟨hys i hi, hlt (c.exsChanges_monotone hi.le)⟩⟩, rfl, rfl⟩⟩;

def Graph (param : V) (x y : V) : Prop := (c.construction L).Fixpoint ![] ⟪param, x, y⟫

variable {param : V}

variable {L c}

lemma Graph.case_iff {p y : V} :
    c.Graph L param p y ↔
    IsUFormula L p ∧ (
    (∃ k R v, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k R v, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋏ p₂ ∧
      y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋎ p₂ ∧
      y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ ys, (len ys = c.allSize param p₁ ∧
        ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i]) ∧
      p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
    (∃ p₁ ys, (len ys = c.exsSize param p₁ ∧
        ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i]) ∧
      p = ^∃ p₁ ∧ y = c.exs param p₁ ys)) :=
  Iff.trans (c.construction L).case (by
    constructor;
    · rintro ⟨param, p', y', e, H⟩;
      rcases show _ = param ∧ p = p' ∧ y = y' by simpa using e with ⟨rfl, rfl, rfl⟩;
      exact H;
    · intro H; exact ⟨_, _, _, rfl, H⟩)

variable (c β)

lemma graph_defined : 𝚺ᴬ₁-Relation₃ c.Graph L via β.graph L := .mk fun v ↦ by
  simp [Blueprint.graph, (c.construction L).fixpoint_defined.iff, Matrix.empty_eq]; rfl;

@[simp] lemma eval_graphDef (v : Fin 3 → V) :
    (β.graph L).val.Evalb v ↔ c.Graph L (v 0) (v 1) (v 2) := (graph_defined β c).iff

instance graph_definable : 𝚺ᴬ-[0 + 1]-Relation₃ c.Graph L := c.graph_defined.to_definable

variable {β c}

section

attribute [local simp] qqRel qqNRel qqVerum qqFalsum qqAnd qqOr qqAll qqExs

lemma graph_rel_iff {k r v y : V} :
    c.Graph L param (^rel k r v) y ↔ IsUFormula L (^rel k r v) ∧ y = c.rel param k r v := by
  rw [Graph.case_iff]; simp;

lemma graph_nrel_iff {k r v y : V} :
    c.Graph L param (^nrel k r v) y ↔ IsUFormula L (^nrel k r v) ∧ y = c.nrel param k r v := by
  rw [Graph.case_iff]; simp;

lemma graph_verum_iff {y : V} : c.Graph L param ^⊤ y ↔ y = c.verum param := by
  rw [Graph.case_iff, and_iff_right IsUFormula.verum]; simp;

lemma graph_falsum_iff {y : V} : c.Graph L param ^⊥ y ↔ y = c.falsum param := by
  rw [Graph.case_iff, and_iff_right IsUFormula.falsum]; simp;

lemma graph_and_iff {p₁ p₂ y : V} :
    c.Graph L param (p₁ ^⋏ p₂) y ↔ IsUFormula L (p₁ ^⋏ p₂) ∧
      ∃ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ y = c.and param p₁ p₂ y₁ y₂ := by
  rw [Graph.case_iff]; simp;

lemma graph_or_iff {p₁ p₂ y : V} :
    c.Graph L param (p₁ ^⋎ p₂) y ↔ IsUFormula L (p₁ ^⋎ p₂) ∧
      ∃ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ y = c.or param p₁ p₂ y₁ y₂ := by
  rw [Graph.case_iff]; simp;

lemma graph_all_iff {p₁ y : V} :
    c.Graph L param (^∀ p₁) y ↔ IsUFormula L (^∀ p₁) ∧ ∃ ys, (len ys = c.allSize param p₁ ∧
      ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i]) ∧
      y = c.all param p₁ ys := by
  rw [Graph.case_iff]; simp;

lemma graph_exs_iff {p₁ y : V} :
    c.Graph L param (^∃ p₁) y ↔ IsUFormula L (^∃ p₁) ∧ ∃ ys, (len ys = c.exsSize param p₁ ∧
      ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i]) ∧
      y = c.exs param p₁ ys := by
  rw [Graph.case_iff]; simp;

end

lemma graph_dom_uformula {p r : V} : c.Graph L param p r → IsUFormula L p :=
  fun h ↦ (Graph.case_iff.mp h).1

variable (param)

lemma graph_exists {p : V} : IsUFormula L p → ∃ y, c.Graph L param p y := by
  have : 𝚺ᴬ₁-Function₂ c.allSize := c.allSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.allChanges := c.allChanges_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsSize := c.exsSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsChanges := c.exsChanges_defined.to_definable;
  let f : V → V → V := fun p param ↦ max param <| max
    (c.allChanges param (c.allSize param (π₂ (p - 1))))
    (c.exsChanges param (c.exsSize param (π₂ (p - 1))));
  have hf : 𝚺ᴬ₁-Function₂ f := by definability;
  apply bounded_all_sigma1_order_induction hf ?_ ?_ p param;
  · definability;
  intro p param ih hp;
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩);
  · exact ⟨_, graph_rel_iff.mpr ⟨hp, rfl⟩⟩;
  · exact ⟨_, graph_nrel_iff.mpr ⟨hp, rfl⟩⟩;
  · exact ⟨_, graph_verum_iff.mpr rfl⟩;
  · exact ⟨_, graph_falsum_iff.mpr rfl⟩;
  · obtain ⟨y₁, h₁⟩ := ih p₁ (by simp) param (by simp [f]) hp₁;
    obtain ⟨y₂, h₂⟩ := ih p₂ (by simp) param (by simp [f]) hp₂;
    exact ⟨_, graph_and_iff.mpr ⟨hp, y₁, y₂, h₁, h₂, rfl⟩⟩;
  · obtain ⟨y₁, h₁⟩ := ih p₁ (by simp) param (by simp [f]) hp₁;
    obtain ⟨y₂, h₂⟩ := ih p₂ (by simp) param (by simp [f]) hp₂;
    exact ⟨_, graph_or_iff.mpr ⟨hp, y₁, y₂, h₁, h₂, rfl⟩⟩;
  · obtain ⟨ys, hys⟩ : ∃ ys, len ys = c.allSize param p₁ ∧
        ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i] :=
      sigmaOne_skolem_vec (by definability) fun i hi ↦
        ih p₁ (by simp) _ (by simp [f, qqAll, c.allChanges_monotone hi.le]) hp₁;
    exact ⟨_, graph_all_iff.mpr ⟨hp, ys, hys, rfl⟩⟩;
  · obtain ⟨ys, hys⟩ : ∃ ys, len ys = c.exsSize param p₁ ∧
        ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i] :=
      sigmaOne_skolem_vec (by definability) fun i hi ↦
        ih p₁ (by simp) _ (by simp [f, qqExs, c.exsChanges_monotone hi.le]) hp₁;
    exact ⟨_, graph_exs_iff.mpr ⟨hp, ys, hys, rfl⟩⟩;

lemma graph_unique {p : V} : IsUFormula L p →
    ∀ {param r r'}, c.Graph L param p r → c.Graph L param p r' → r = r' := by
  apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p ↦ ∀ {param r r'},
    c.Graph L param p r → c.Graph L param p r' → r = r') (by definability);
  case hrel => intro k R v _ _ param r r' hr hr'; simp_all [graph_rel_iff];
  case hnrel => intro k R v _ _ param r r' hr hr'; simp_all [graph_nrel_iff];
  case hverum => intro param r r' hr hr'; simp_all [graph_verum_iff];
  case hfalsum => intro param r r' hr hr'; simp_all [graph_falsum_iff];
  case hand =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr';
    obtain ⟨-, r₁, r₂, h₁, h₂, rfl⟩ := graph_and_iff.mp hr;
    obtain ⟨-, r₁', r₂', h₁', h₂', rfl⟩ := graph_and_iff.mp hr';
    rw [ih₁ h₁ h₁', ih₂ h₂ h₂'];
  case hor =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr';
    obtain ⟨-, r₁, r₂, h₁, h₂, rfl⟩ := graph_or_iff.mp hr;
    obtain ⟨-, r₁', r₂', h₁', h₂', rfl⟩ := graph_or_iff.mp hr';
    rw [ih₁ h₁ h₁', ih₂ h₂ h₂'];
  case hall =>
    intro p₁ _ ih param r r' hr hr';
    obtain ⟨-, ys, ⟨hl, hys⟩, rfl⟩ := graph_all_iff.mp hr;
    obtain ⟨-, ys', ⟨hl', hys'⟩, rfl⟩ := graph_all_iff.mp hr';
    rw [nth_ext (hl.trans hl'.symm) fun i hi ↦ ih (hys i (hl ▸ hi)) (hys' i (hl ▸ hi))];
  case hexs =>
    intro p₁ _ ih param r r' hr hr';
    obtain ⟨-, ys, ⟨hl, hys⟩, rfl⟩ := graph_exs_iff.mp hr;
    obtain ⟨-, ys', ⟨hl', hys'⟩, rfl⟩ := graph_exs_iff.mp hr';
    rw [nth_ext (hl.trans hl'.symm) fun i hi ↦ ih (hys i (hl ▸ hi)) (hys' i (hl ▸ hi))];

variable (L c)

lemma exists_unique_all (p : V) :
    ∃! r, (IsUFormula L p → c.Graph L param p r) ∧ (¬IsUFormula L p → r = 0) := by
  by_cases hp : IsUFormula L p;
  · obtain ⟨r, hr⟩ := graph_exists (c := c) param hp;
    exact ⟨r, by simp [hp, hr], fun r' hr' ↦ graph_unique hp (by simpa [hp] using hr') hr⟩;
  · simp [hp];

noncomputable def result (p : V) : V := Classical.choose! (c.exists_unique_all L param p)

variable {L c}

lemma result_prop {p : V} (hp : IsUFormula L p) : c.Graph L param p (c.result L param p) :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬IsUFormula L p) : c.result L param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r : V} (h : c.Graph L param p r) : c.result L param p = r :=
  graph_unique (graph_dom_uformula h) (result_prop (c := c) param (graph_dom_uformula h)) h

@[simp] lemma result_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^rel k R v) = c.rel param k R v :=
  result_eq_of_graph <| graph_rel_iff.mpr ⟨by simp [hR, hv], rfl⟩

@[simp] lemma result_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^nrel k R v) = c.nrel param k R v :=
  result_eq_of_graph <| graph_nrel_iff.mpr ⟨by simp [hR, hv], rfl⟩

@[simp] lemma result_verum : c.result L param ^⊤ = c.verum param :=
  result_eq_of_graph <| graph_verum_iff.mpr rfl

@[simp] lemma result_falsum : c.result L param ^⊥ = c.falsum param :=
  result_eq_of_graph <| graph_falsum_iff.mpr rfl

@[simp] lemma result_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋏ q) = c.and param p q (c.result L param p) (c.result L param q) :=
  result_eq_of_graph <| graph_and_iff.mpr
    ⟨by simp [hp, hq], _, _, result_prop param hp, result_prop param hq, rfl⟩

@[simp] lemma result_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋎ q) = c.or param p q (c.result L param p) (c.result L param q) :=
  result_eq_of_graph <| graph_or_iff.mpr
    ⟨by simp [hp, hq], _, _, result_prop param hp, result_prop param hq, rfl⟩

lemma result_all {p : V} (hp : IsUFormula L p) :
    ∃ ys, (len ys = c.allSize param p ∧
      ∀ i < c.allSize param p, ys.[i] = c.result L (c.allChanges param i) p) ∧
      c.result L param (^∀ p) = c.all param p ys := by
  obtain ⟨-, ys, ⟨hl, hys⟩, h⟩ := graph_all_iff.mp (result_prop (c := c) param (by simpa using hp));
  exact ⟨ys, ⟨hl, fun i hi ↦ (result_eq_of_graph (hys i hi)).symm⟩, h⟩;

lemma result_exs {p : V} (hp : IsUFormula L p) :
    ∃ ys, (len ys = c.exsSize param p ∧
      ∀ i < c.exsSize param p, ys.[i] = c.result L (c.exsChanges param i) p) ∧
      c.result L param (^∃ p) = c.exs param p ys := by
  obtain ⟨-, ys, ⟨hl, hys⟩, h⟩ := graph_exs_iff.mp (result_prop (c := c) param (by simpa using hp));
  exact ⟨ys, ⟨hl, fun i hi ↦ (result_eq_of_graph (hys i hi)).symm⟩, h⟩;

variable (c β)

lemma result_defined : 𝚺ᴬ₁-Function₂ c.result L via β.result L := .mk fun v ↦ by
  simp [Blueprint.result, result, c.eval_graphDef];

instance result_definable : 𝚺ᴬ-[0 + 1]-Function₂ c.result L := c.result_defined.to_definable

end Construction

end UformulaFamilyRec

end FFL.FirstOrder.Arithmetic.Bootstrapping
