module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
set_option autoImplicit true
namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Recursion on formulas -/

namespace UformulaRec1

structure Blueprint where
  rel : 𝚺ᴬ₁.Semisentence 5
  nrel : 𝚺ᴬ₁.Semisentence 5
  verum : 𝚺ᴬ₁.Semisentence 2
  falsum : 𝚺ᴬ₁.Semisentence 2
  and : 𝚺ᴬ₁.Semisentence 6
  or : 𝚺ᴬ₁.Semisentence 6
  all : 𝚺ᴬ₁.Semisentence 4
  allSize : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “n param p. n = 1”
  allChanges : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “param' param i. param' = param”
  exs : 𝚺ᴬ₁.Semisentence 4
  exsSize : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “n param p. n = 1”
  exsChanges : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “param' param i. param' = param”

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

/-- Note: `noncomputable` attribute to prohibit compilation of a large term. This is necessary for
  Zoo and integration with Verso. -/
noncomputable def graph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param p y. ∃ pr, !pair₃Def pr param p y ∧ !(β.blueprint L).fixpointDef pr”

/-- Note: `noncomputable` attribute to prohibit compilation of a large term. This is necessary for
  Zoo and integration with Verso. -/
noncomputable def result : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y param p. (!(isUFormula L).pi p → !(β.graph L) param p y) ∧ (¬!(isUFormula L).sigma p → y = 0)”

end Blueprint

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma one_defined : 𝚺ᴬ₁-Function₂ (fun _ _ ↦ 1 : V → V → V) via .mkSigma “n param p. n = 1” :=
  .mk fun v ↦ by simp

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma param_defined :
    𝚺ᴬ₁-Function₂ (fun param _ ↦ param : V → V → V) via .mkSigma “param' param i. param' = param” :=
  .mk fun v ↦ by simp

variable (V)

/-- The value at `^∀ p` is `all param p ys`, where `ys` is the vector of the values of `p` at the
  parameters `allChanges param i` for `i < allSize param p`; likewise at `^∃ p`. -/
structure Construction (φ : Blueprint) where
  rel (param k R v : V) : V
  nrel (param k R v : V) : V
  verum (param : V) : V
  falsum (param : V) : V
  and (param p₁ p₂ y₁ y₂ : V) : V
  or (param p₁ p₂ y₁ y₂ : V) : V
  all (param p₁ ys : V) : V
  allSize (param p₁ : V) : V := 1
  allChanges (param i : V) : V := param
  exs (param p₁ ys : V) : V
  exsSize (param p₁ : V) : V := 1
  exsChanges (param i : V) : V := param
  rel_defined : 𝚺ᴬ₁-Function₄ rel via φ.rel
  nrel_defined : 𝚺ᴬ₁-Function₄ nrel via φ.nrel
  verum_defined : 𝚺ᴬ₁-Function₁ verum via φ.verum
  falsum_defined : 𝚺ᴬ₁-Function₁ falsum via φ.falsum
  and_defined : 𝚺ᴬ₁-Function₅ and via φ.and
  or_defined : 𝚺ᴬ₁-Function₅ or via φ.or
  all_defined : 𝚺ᴬ₁-Function₃ all via φ.all
  allSize_defined : 𝚺ᴬ₁-Function₂ allSize via φ.allSize := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.one_defined
  allChanges_defined : 𝚺ᴬ₁-Function₂ allChanges via φ.allChanges := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.param_defined
  exs_defined : 𝚺ᴬ₁-Function₃ exs via φ.exs
  exsSize_defined : 𝚺ᴬ₁-Function₂ exsSize via φ.exsSize := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.one_defined
  exsChanges_defined : 𝚺ᴬ₁-Function₂ exsChanges via φ.exsChanges := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.param_defined
  allChanges_monotone {param i j : V} : i ≤ j → allChanges param i ≤ allChanges param j := by
    intros; exact le_rfl
  exsChanges_monotone {param i j : V} : i ≤ j → exsChanges param i ≤ exsChanges param j := by
    intros; exact le_rfl

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

variable {L}

lemma result_prop {p : V} (hp : IsUFormula L p) : c.Graph L param p (c.result L param p) :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬IsUFormula L p) : c.result L param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r : V} (h : c.Graph L param p r) : c.result L param p = r :=
  graph_unique (graph_dom_uformula h) (c.result_prop param (graph_dom_uformula h)) h

@[simp] lemma result_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^rel k R v) = c.rel param k R v :=
  c.result_eq_of_graph <| graph_rel_iff.mpr ⟨by simp [hR, hv], rfl⟩

@[simp] lemma result_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^nrel k R v) = c.nrel param k R v :=
  c.result_eq_of_graph <| graph_nrel_iff.mpr ⟨by simp [hR, hv], rfl⟩

@[simp] lemma result_verum : c.result L param ^⊤ = c.verum param :=
  c.result_eq_of_graph <| graph_verum_iff.mpr rfl

@[simp] lemma result_falsum : c.result L param ^⊥ = c.falsum param :=
  c.result_eq_of_graph <| graph_falsum_iff.mpr rfl

@[simp] lemma result_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋏ q) = c.and param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph <| graph_and_iff.mpr
    ⟨by simp [hp, hq], _, _, c.result_prop param hp, c.result_prop param hq, rfl⟩

@[simp] lemma result_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋎ q) = c.or param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph <| graph_or_iff.mpr
    ⟨by simp [hp, hq], _, _, c.result_prop param hp, c.result_prop param hq, rfl⟩

lemma exists_result_all {p : V} (hp : IsUFormula L p) :
    ∃ ys, (len ys = c.allSize param p ∧
      ∀ i < c.allSize param p, ys.[i] = c.result L (c.allChanges param i) p) ∧
      c.result L param (^∀ p) = c.all param p ys := by
  obtain ⟨-, ys, ⟨hl, hys⟩, h⟩ := graph_all_iff.mp (c.result_prop param (by simpa using hp));
  exact ⟨ys, ⟨hl, fun i hi ↦ (c.result_eq_of_graph (hys i hi)).symm⟩, h⟩;

lemma exists_result_exs {p : V} (hp : IsUFormula L p) :
    ∃ ys, (len ys = c.exsSize param p ∧
      ∀ i < c.exsSize param p, ys.[i] = c.result L (c.exsChanges param i) p) ∧
      c.result L param (^∃ p) = c.exs param p ys := by
  obtain ⟨-, ys, ⟨hl, hys⟩, h⟩ := graph_exs_iff.mp (c.result_prop param (by simpa using hp));
  exact ⟨ys, ⟨hl, fun i hi ↦ (c.result_eq_of_graph (hys i hi)).symm⟩, h⟩;

@[simp] lemma result_all {p : V} (hp : IsUFormula L p) (hs : c.allSize param p = 1) :
    c.result L param (^∀ p) = c.all param p ?[c.result L (c.allChanges param 0) p] :=
  c.result_eq_of_graph <| graph_all_iff.mpr ⟨by simpa using hp, _, ⟨by simp [hs], fun i hi ↦ by
    rcases lt_one_iff_eq_zero.mp (hs ▸ hi); simpa using c.result_prop _ hp⟩, rfl⟩

@[simp] lemma result_exs {p : V} (hp : IsUFormula L p) (hs : c.exsSize param p = 1) :
    c.result L param (^∃ p) = c.exs param p ?[c.result L (c.exsChanges param 0) p] :=
  c.result_eq_of_graph <| graph_exs_iff.mpr ⟨by simpa using hp, _, ⟨by simp [hs], fun i hi ↦ by
    rcases lt_one_iff_eq_zero.mp (hs ▸ hi); simpa using c.result_prop _ hp⟩, rfl⟩

variable (β)

lemma result_defined : 𝚺ᴬ₁-Function₂ c.result L via β.result L := .mk fun v ↦ by
  simp [Blueprint.result, result, c.eval_graphDef];

instance result_definable : 𝚺ᴬ-[0 + 1]-Function₂ c.result L := c.result_defined.to_definable

variable {β}

lemma uformula_result_induction {P : V → V → V → Prop} (hP : 𝚺ᴬ₁-Relation₃ P)
    (hRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v →
      P param (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v →
      P param (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param ^⊤ (c.verum param))
    (hfalsum : ∀ param, P param ^⊥ (c.falsum param))
    (hand : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) →
      P param (p ^⋏ q) (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) →
      P param (p ^⋎ q) (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ param p, IsUFormula L p →
      (∀ i < c.allSize param p,
        P (c.allChanges param i) p (c.result L (c.allChanges param i) p)) →
      P param (^∀ p) (c.result L param (^∀ p)))
    (hexs : ∀ param p, IsUFormula L p →
      (∀ i < c.exsSize param p,
        P (c.exsChanges param i) p (c.result L (c.exsChanges param i) p)) →
      P param (^∃ p) (c.result L param (^∃ p))) :
    ∀ {param p : V}, IsUFormula L p → P param p (c.result L param p) := by
  have : 𝚺ᴬ₁-Function₂ c.result L := c.result_definable;
  have : 𝚺ᴬ₁-Function₂ c.allSize := c.allSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.allChanges := c.allChanges_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsSize := c.exsSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsChanges := c.exsChanges_defined.to_definable;
  let f : V → V → V := fun p param ↦ max param <| max
    (c.allChanges param (c.allSize param (π₂ (p - 1))))
    (c.exsChanges param (c.exsSize param (π₂ (p - 1))));
  have hf : 𝚺ᴬ₁-Function₂ f := by definability;
  intro param p;
  apply bounded_all_sigma1_order_induction hf ?_ ?_ p param;
  · apply Bounding.HierarchySymbol.Definable.imp
      (Bounding.HierarchySymbol.Definable.comp₁ (Bounding.HierarchySymbol.DefinableFunction.var _))
      (Bounding.HierarchySymbol.Definable.comp₃
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction₂.comp
          (Bounding.HierarchySymbol.DefinableFunction.var _)
          (Bounding.HierarchySymbol.DefinableFunction.var _)));
  intro p param ih hp;
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩);
  · simpa [hkr, hv] using hRel param k r v hkr hv;
  · simpa [hkr, hv] using hNRel param k r v hkr hv;
  · simpa using hverum param;
  · simpa using hfalsum param;
  · simpa [hp₁, hp₂] using hand param p₁ p₂ hp₁ hp₂
      (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by simp [f]) hp₂);
  · simpa [hp₁, hp₂] using hor param p₁ p₂ hp₁ hp₂
      (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by simp [f]) hp₂);
  · exact hall param p₁ hp₁ fun i hi ↦
      ih p₁ (by simp) _ (by simp [f, qqAll, c.allChanges_monotone hi.le]) hp₁;
  · exact hexs param p₁ hp₁ fun i hi ↦
      ih p₁ (by simp) _ (by simp [f, qqExs, c.exsChanges_monotone hi.le]) hp₁;

end Construction

end UformulaRec1

/-! ### Bound variables -/

section bv

variable {Γ : Polarity} {m : ℕ}

namespace BV

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(termBVVecGraph L) M k v ∧ !listMaxDef y M”
  nrel := .mkSigma “y param k R v. ∃ M, !(termBVVecGraph L) M k v ∧ !listMaxDef y M”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !subDef y y₁ 1”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !subDef y y₁ 1”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  nrel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ ys ↦ ys.[0] - 1
  exs {_} := fun _ ys ↦ ys.[0] - 1
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end BV

open BV

variable (L)

noncomputable def bv (p : V) : V := (BV.construction L).result L 0 p

noncomputable def bvGraph : 𝚺ᴬ₁.Semisentence 2 := ((BV.blueprint L).result L).rew (Rew.subst ![#0,
  ‘0’, #1])

variable {L}

section

instance bv.defined : 𝚺ᴬ₁-Function₁ bv (V := V) L via bvGraph L := .mk fun v ↦ by
  simpa [bvGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! (BV.construction
    L).result_defined.defined ![v 0, 0, v 1]

instance bv.definable : 𝚺ᴬ₁-Function₁ bv (V := V) L := bv.defined.to_definable

instance bv.definable' : Γᴬ-[m + 1]-Function₁ bv (V := V) L := bv.definable.of_sigmaOne

end

@[simp] lemma bv_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^rel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^nrel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_verum : bv L (^⊤ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_falsum : bv L (^⊥ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋏ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, BV.construction]

@[simp] lemma bv_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋎ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, construction]

@[simp] lemma bv_all {p : V} (hp : IsUFormula L p) : bv L (^∀ p) = bv L p - 1 := by simp [bv, hp,
  construction]

@[simp] lemma bv_ex {p : V} (hp : IsUFormula L p) : bv L (^∃ p) = bv L p - 1 := by simp [bv, hp,
  construction]

lemma bv_eq_of_not_isUFormula {p : V} (h : ¬IsUFormula L p) : bv L p = 0 := (construction
  L).result_prop_not _ h

end bv

/-! ### Semiformulas -/

section isSemiformula

variable {Γ : Polarity} {m : ℕ}

variable (L)

structure IsSemiformula (n p : V) : Prop where
  isUFormula : IsUFormula L p
  bv_le : bv L p ≤ n

abbrev IsFormula (p : V) : Prop := IsSemiformula L 0 p

noncomputable def isSemiformula : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !(isUFormula L).sigma p ∧ ∃ b, !(bvGraph L) b p ∧ b ≤ n”)
  (.mkPi “n p. !(isUFormula L).pi p ∧ ∀ b, !(bvGraph L) b p → b ≤ n”)

variable {L}

lemma isSemiformula_iff {n p : V} :
    IsSemiformula L n p ↔ IsUFormula L p ∧ bv L p ≤ n :=
  ⟨fun h ↦ ⟨h.isUFormula, h.bv_le⟩, by rintro ⟨hp, h⟩; exact ⟨hp, h⟩⟩

section

instance IsSemiformula.defined : 𝚫ᴬ₁-Relation IsSemiformula (V := V) L via isSemiformula L := .mk <|
  by
  constructor
  · intro v; simp [isSemiformula, Bounding.HierarchySymbol.Semiformula.val_sigma, bv.defined.iff]
  · intro v; simp [isSemiformula, Bounding.HierarchySymbol.Semiformula.val_sigma, bv.defined.iff,
    isSemiformula_iff]

instance IsSemiformula.definable : 𝚫ᴬ₁-Relation IsSemiformula (V := V) L :=
  IsSemiformula.defined.to_definable

instance IsSemiformula.definable' : Γᴬ-[m + 1]-Relation IsSemiformula (V := V) L :=
  IsSemiformula.definable.of_deltaOne

end

@[simp] lemma IsUFormula.isSemiformula {p : V} (h : IsUFormula L p) : IsSemiformula L (bv L p) p
  where
  isUFormula := h
  bv_le := by rfl

@[simp] lemma IsSemiformula.rel {n k r v : V} :
    IsSemiformula L n (^rel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun {i} hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_rel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.nrel {n k r v : V} :
    IsSemiformula L n (^nrel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun {i} hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_nrel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.verum {n : V} : IsSemiformula L n ^⊤ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.falsum {n : V} : IsSemiformula L n ^⊥ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.and {n p q : V} :
    IsSemiformula L n (p ^⋏ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le,
      hq.bv_le]⟩

@[simp] lemma IsSemiformula.or {n p q : V} :
    IsSemiformula L n (p ^⋎ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le,
      hq.bv_le]⟩

@[simp] lemma IsSemiformula.all {n p : V} :
    IsSemiformula L n (^∀ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

@[simp] lemma IsSemiformula.exs {n p : V} :
    IsSemiformula L n (^∃ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

lemma IsSemiformula.case_iff {n p : V} :
    IsSemiformula L n p ↔
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∃ p₁) := by
  constructor
  · intro h
    rcases h.isUFormula.case with
      (⟨k, r, v, _, _, rfl⟩ | ⟨k, r, v, _, _, rfl⟩ | rfl | rfl | ⟨p₁, p₂, _, _, rfl⟩ | ⟨p₁, p₂, _,
        _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩)
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      disj 1; exact ⟨k, r, v, by simp [this]⟩;
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      disj 2; exact ⟨k, r, v, by simp [this]⟩;
    · disj 3; rfl;
    · disj 4; rfl;
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      disj 5; exact ⟨p₁, p₂, by simp [this]⟩;
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      disj 6; exact ⟨p₁, p₂, by simp [this]⟩;
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      disj 7; exact ⟨p₁, by simp [this]⟩;
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      disj 8; exact ⟨p₁, by simp [this]⟩;
  · rintro (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩) <;> simp [*]

lemma IsSemiformula.case {P : V → V → Prop} {n p} (hp : IsSemiformula L n p)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P n (^∃ p)) : P n p := by
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂,
      h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ _ hR hv
  · exact hnrel _ _ _ _ hR hv
  · exact hverum n
  · exact hfalsum n
  · exact hand _ _ _ h₁ h₂
  · exact hor _ _ _ h₁ h₂
  · exact hall _ _ h₁
  · exact hexs _ _ h₁

lemma IsSemiformula.sigma1_structural_induction {P : V → V → Prop} (hP : 𝚺ᴬ₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p := by
  have : 𝚺ᴬ₁-Function₂ (fun _ (n : V) ↦ n + 1) := by definability
  apply bounded_all_sigma1_order_induction this ?_ ?_ p n
  · apply Bounding.HierarchySymbol.Definable.imp
    · exact Bounding.HierarchySymbol.Definable.comp₂
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _)
    · exact Bounding.HierarchySymbol.Definable.comp₂
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _)
  intro p n ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂,
      h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · apply hrel _ _ _ _ hR hv
  · apply hnrel _ _ _ _ hR hv
  · apply hverum
  · apply hfalsum
  · apply hand _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hor _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hall _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)
  · apply hexs _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)

lemma IsSemiformula.pi1_structural_induction {P : V → V → Prop} (hP : 𝚷ᴬ₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p := by
  suffices IsUFormula L p → ∀ n, IsSemiformula L n p → P n p by intro h; exact this h.isUFormula n h
  apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p ↦ ∀ n, IsSemiformula L n p → P n p)
  · definability
  · intro k R v hR _ n h
    have : L.IsRel k R ∧ IsSemitermVec L k n v := by simpa using h
    exact hrel _ _ _ _ hR this.2
  · intro k R v hR _ n h
    have : L.IsRel k R ∧ IsSemitermVec L k n v := by simpa using h
    exact hnrel _ _ _ _ hR this.2
  · intro n _; apply hverum
  · intro n _; apply hfalsum
  · intro p q _ _ ihp ihq n h
    have : IsSemiformula L n p ∧ IsSemiformula L n q := by simpa using h
    apply hand _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p q _ _ ihp ihq n h
    have : IsSemiformula L n p ∧ IsSemiformula L n q := by simpa using h
    apply hor _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p _ ihp n h
    have : IsSemiformula L (n + 1) p := by simpa using h
    apply hall _ _ this (ihp _ this)
  · intro p _ ihp n h
    have : IsSemiformula L (n + 1) p := by simpa using h
    apply hexs _ _ this (ihp _ this)

lemma IsSemiformula.induction1 (Γ) {P : V → V → Prop} (hP : Γᴬ-[1]-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p :=
  match Γ with
  | 𝚺 => IsSemiformula.sigma1_structural_induction hP hrel hnrel hverum hfalsum hand hor hall hexs
  | 𝚷 => IsSemiformula.pi1_structural_induction hP hrel hnrel hverum hfalsum hand hor hall hexs
  | 𝚫 => IsSemiformula.sigma1_structural_induction hP.of_delta hrel hnrel hverum hfalsum hand hor
    hall hexs


lemma IsSemiformula.pos {n p : V} (h : IsSemiformula L n p) : 0 < p := h.isUFormula.pos

@[simp] lemma IsSemiformula.not_zero (m : V) : ¬IsSemiformula L m (0 : V) := by intro h; simpa
  using h.pos

end isSemiformula

namespace UformulaRec1.Construction

variable {β : Blueprint} {c : Construction V β}

lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : 𝚺ᴬ₁-Relation₄ P)
    (hrel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v →
      P param n (^rel k R v) (c.rel param k R v))
    (hnrel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v →
      P param n (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ n param, P param n ^⊤ (c.verum param))
    (hfalsum : ∀ n param, P param n ^⊥ (c.falsum param))
    (hand : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) →
      P param n (p ^⋏ q) (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) →
      P param n (p ^⋎ q) (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ n param p, IsSemiformula L (n + 1) p →
      (∀ i < c.allSize param p,
        P (c.allChanges param i) (n + 1) p (c.result L (c.allChanges param i) p)) →
      P param n (^∀ p) (c.result L param (^∀ p)))
    (hexs : ∀ n param p, IsSemiformula L (n + 1) p →
      (∀ i < c.exsSize param p,
        P (c.exsChanges param i) (n + 1) p (c.result L (c.exsChanges param i) p)) →
      P param n (^∃ p) (c.result L param (^∃ p))) :
    ∀ {param n p : V}, IsSemiformula L n p → P param n p (c.result L param p) := by
  have : 𝚺ᴬ₁-Function₂ c.result L := c.result_definable;
  have : 𝚺ᴬ₁-Function₂ c.allSize := c.allSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.allChanges := c.allChanges_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsSize := c.exsSize_defined.to_definable;
  have : 𝚺ᴬ₁-Function₂ c.exsChanges := c.exsChanges_defined.to_definable;
  let f : V → V → V → V := fun p param _ ↦ max param <| max
    (c.allChanges param (c.allSize param (π₂ (p - 1))))
    (c.exsChanges param (c.exsSize param (π₂ (p - 1))));
  have hf : 𝚺ᴬ₁-Function₃ f := by definability;
  let g : V → V → V → V := fun _ _ n ↦ n + 1;
  have hg : 𝚺ᴬ₁-Function₃ g := by definability;
  intro param n p;
  apply bounded_all_sigma1_order_induction₂ hf hg ?_ ?_ p param n;
  · apply Bounding.HierarchySymbol.Definable.imp;
    · exact Bounding.HierarchySymbol.Definable.comp₂
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _);
    · apply Bounding.HierarchySymbol.Definable.comp₄
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _);
      exact Bounding.HierarchySymbol.DefinableFunction₂.comp
        (Bounding.HierarchySymbol.DefinableFunction.var _)
        (Bounding.HierarchySymbol.DefinableFunction.var _);
  intro p param n ih hp;
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
      ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩);
  · simpa [hR, hv.isUTerm] using hrel n param k R v hR hv;
  · simpa [hR, hv.isUTerm] using hnrel n param k R v hR hv;
  · simpa using hverum n param;
  · simpa using hfalsum n param;
  · simpa [h₁.isUFormula, h₂.isUFormula] using hand n param p₁ p₂ h₁ h₂
      (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
      (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂);
  · simpa [h₁.isUFormula, h₂.isUFormula] using hor n param p₁ p₂ h₁ h₂
      (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
      (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂);
  · exact hall n param p₁ h₁ fun i hi ↦
      ih p₁ (by simp) _ (by simp [f, qqAll, c.allChanges_monotone hi.le]) (n + 1) (by simp [g]) h₁;
  · exact hexs n param p₁ h₁ fun i hi ↦
      ih p₁ (by simp) _ (by simp [f, qqExs, c.exsChanges_monotone hi.le]) (n + 1) (by simp [g]) h₁;

end UformulaRec1.Construction

/-! ### Negation function -/

section negation

namespace Negation

def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !qqNRelDef y k R v”
  nrel := .mkSigma “y param k R v. !qqRelDef y k R v”
  verum := .mkSigma “y param. !qqFalsumDef y”
  falsum := .mkSigma “y param. !qqVerumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqExsDef y y₁”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqAllDef y y₁”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun k R v ↦ ^nrel k R v
  nrel {_} := fun k R v ↦ ^rel k R v
  verum {_} := ^⊥
  falsum {_} := ^⊤
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  all {_} := fun _ ys ↦ ^∃ ys.[0]
  exs {_} := fun _ ys ↦ ^∀ ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end Negation

open Negation

variable (L)

noncomputable def neg (p : V) : V := construction.result L 0 p

noncomputable def negGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (blueprint.result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

instance neg.defined : 𝚺ᴬ₁-Function₁ neg (V := V) L via negGraph L  := .mk fun v ↦ by
  simpa [negGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! construction.result_defined.defined ![v 0, 0, v 1]

instance neg.definable : 𝚺ᴬ₁-Function₁ neg (V := V) L := neg.defined.to_definable

instance neg.definable' (Γ m) : Γᴬ-[m + 1]-Function₁ neg (V := V) L := .of_sigmaOne neg.definable

end

@[simp] lemma neg_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^rel k R v) = ^nrel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^nrel k R v) = ^rel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_verum :
    neg L (^⊤ : V) = ^⊥ := by simp [neg, construction]

@[simp] lemma neg_falsum :
    neg L (^⊥ : V) = ^⊤ := by simp [neg, construction]

@[simp] lemma neg_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋏ q) = neg L p ^⋎ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋎ q) = neg L p ^⋏ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_all {p : V} (hp : IsUFormula L p) :
    neg L (^∀ p) = ^∃ (neg L p) := by simp [neg, hp, construction]

@[simp] lemma neg_ex {p : V} (hp : IsUFormula L p) :
    neg L (^∃ p) = ^∀ (neg L p) := by simp [neg, hp, construction]

lemma neg_not_uformula {x : V} (h : ¬IsUFormula L x) :
    neg L x = 0 := construction.result_prop_not _ h

lemma IsUFormula.neg {p : V} : IsUFormula L p → IsUFormula L (neg L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma IsUFormula.bv_neg {p : V} :
    IsUFormula L p → bv L (Bootstrapping.neg L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R v hR hv; simp [*]
  · intro k R v hR hv; simp [*]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_neg {p : V} :
    IsUFormula L p → Bootstrapping.neg L (Bootstrapping.neg L p) = p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_iff {p : V} :
    IsUFormula L (Bootstrapping.neg L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    contradiction
  · exact IsUFormula.neg

@[simp] lemma IsSemiformula.neg_iff {n p : V} :
    IsSemiformula L n (neg L p) ↔ IsSemiformula L n p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    have : IsSemiformula L n p := ⟨Hp, by simpa [Hp.bv_neg] using h.bv_le⟩
    contradiction
  · intro h; exact ⟨by simp [h.isUFormula], by simpa [h.isUFormula] using h.bv_le⟩

alias ⟨IsSemiformula.elim_neg, IsSemiformula.neg⟩ := IsSemiformula.neg_iff

@[simp] lemma neg_inj_iff {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L p = neg L q ↔ p = q := by
  constructor
  · intro h; simpa [hp.neg_neg, hq.neg_neg] using congrArg (neg L) h
  · rintro rfl; rfl

end negation

variable (L)

noncomputable def imp (p q : V) : V := neg L p ^⋎ q

notation:60 p:61 " ^→[" L "] " q:60 => Language.imp L p q

noncomputable def impGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “r p q. ∃ np, !(negGraph L) np p ∧ !qqOrDef r np q”

noncomputable def iff (p q : V) : V := (imp L p q) ^⋏ (imp L q p)

noncomputable def iffGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “r p q. ∃ pq, !(impGraph L) pq p q ∧ ∃ qp, !(impGraph L) qp q p ∧ !qqAndDef r pq qp”

variable {L}

section imp

@[simp] lemma IsUFormula.imp {p q : V} :
    IsUFormula L (imp L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp [Bootstrapping.imp]

@[simp] lemma IsSemiformula.imp {n p q : V} :
    IsSemiformula L n (imp L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp [Bootstrapping.imp]

section

instance imp.defined : 𝚺ᴬ₁-Function₂ imp (V := V) L via impGraph L :=
  .mk fun v ↦ by simp [impGraph]; rfl

instance imp.definable : 𝚺ᴬ₁-Function₂ imp (V := V) L := imp.defined.to_definable

instance imp.definable' (Γ m) : Γᴬ-[m + 1]-Function₂ imp (V := V) L := imp.definable.of_sigmaOne

end

end imp

section iff

@[simp] lemma IsUFormula.iff {p q : V} :
    IsUFormula L (iff L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma IsSemiformula.iff {n p q : V} :
    IsSemiformula L n (iff L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma lt_iff_left (p q : V) : p < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_right _ _)

@[simp] lemma lt_iff_right (p q : V) : q < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_left _ _)

section

instance iff.defined : 𝚺ᴬ₁-Function₂ iff (V := V) L via iffGraph L :=
  .mk fun v ↦ by simp [iffGraph]; rfl

instance iff.definable : 𝚺ᴬ₁-Function₂ iff (V := V) L := iff.defined.to_definable

instance iff_definable' (Γ m) : Γᴬ-[m + 1]-Function₂ iff (V := V) L := iff.definable.of_sigmaOne

end

end iff

/-! ### Shift function -/

section shift

namespace Shift

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqAllDef y y₁”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqExsDef y y₁”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k R v ↦ ^rel k R (termShiftVec L k v)
  nrel {_} := fun k R v ↦ ^nrel k R (termShiftVec L k v)
  verum {_} := ^⊤
  falsum {_} := ^⊥
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all {_} := fun _ ys ↦ ^∀ ys.[0]
  exs {_} := fun _ ys ↦ ^∃ ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end Shift

open Shift

variable (L)

noncomputable def shift (p : V) : V := (construction L).result L 0 p

noncomputable def shiftGraph : 𝚺ᴬ₁.Semisentence 2 :=
  blueprint L |>.result L |>.rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

instance shift.defined : 𝚺ᴬ₁-Function₁[V] shift L via shiftGraph L := .mk fun v ↦ by
  simpa [shiftGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! (construction L).result_defined.defined ![v 0, 0, v 1]

instance shift.definable : 𝚺ᴬ₁-Function₁[V] shift L := shift.defined.to_definable

instance shift.definable' (Γ m) : Γᴬ-[m + 1]-Function₁[V] shift L := shift.definable.of_sigmaOne

end

@[simp] lemma shift_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^relk R v) = ^relk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]

@[simp] lemma shift_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^nrelk R v) = ^nrelk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]

@[simp] lemma shift_verum : shift L (^⊤ : V) = ^⊤ := by simp [shift, construction]

@[simp] lemma shift_falsum : shift L (^⊥ : V) = ^⊥ := by simp [shift, construction]

@[simp] lemma shift_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋏ q) = shift L p ^⋏ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋎ q) = shift L p ^⋎ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_all {p : V} (hp : IsUFormula L p) :
    shift L (^∀ p) = ^∀ (shift L p) := by simp [shift, hp, construction]

@[simp] lemma shift_exs {p : V} (hp : IsUFormula L p) :
    shift L (^∃ p) = ^∃ (shift L p) := by simp [shift, hp, construction]

lemma shift_not_uformula {x : V} (h : ¬IsUFormula L x) :
    shift L x = 0 := (construction L).result_prop_not _ h

lemma IsUFormula.shift {p : V} : IsUFormula L p → IsUFormula L (shift L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma IsUFormula.bv_shift {p : V} : IsUFormula L p → bv L (Bootstrapping.shift L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]

lemma IsSemiformula.shift {p : V} : IsSemiformula L n p → IsSemiformula L n (shift L p) := by
  apply IsSemiformula.sigma1_structural_induction
  · definability
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]

@[simp] lemma IsUFormula.shift_iff {p : V} :
    IsUFormula L (Bootstrapping.shift L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    contradiction
  · exact IsUFormula.shift

@[simp] lemma IsSemiformula.shift_iff {p : V} :
    IsSemiformula L n (Bootstrapping.shift L p) ↔ IsSemiformula L n p :=
  ⟨fun h ↦ by
    have : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    exact ⟨this, by simpa [this.bv_shift] using h.bv_le⟩,
    IsSemiformula.shift⟩

lemma shift_neg {p : V} (hp : IsSemiformula L n p) : shift L (neg L p) = neg L (shift L p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]

end shift

/-! ### Substitution function -/

section subst

namespace Substs

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧
      !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all    := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqAllDef y y₁”
  exs    := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ !qqExsDef y y₁”
  allChanges := .mkSigma “param' param i. !(qVecGraph L) param' param”
  exsChanges := .mkSigma “param' param i. !(qVecGraph L) param' param”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel (param)  := fun k R v ↦ ^rel k R (termSubstVec L k param v)
  nrel (param) := fun k R v ↦ ^nrel k R (termSubstVec L k param v)
  verum _      := ^⊤
  falsum _     := ^⊥
  and _        := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _         := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _        := fun _ ys ↦ ^∀ ys.[0]
  exs _        := fun _ ys ↦ ^∃ ys.[0]
  allChanges param _ := qVec L param
  exsChanges param _ := qVec L param
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  -- Letting `simp` apply `Semiformula.eval_substs` here overflows memory on Lean v4.33.1.
  allChanges_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]
  exsChanges_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]

end Substs

open Substs

variable (L)

noncomputable def subst (w p : V) : V := (construction L).result L w p

noncomputable def substsGraph : 𝚺ᴬ₁.Semisentence 3 := (blueprint L).result L

variable {L}

section

instance subst.defined : 𝚺ᴬ₁-Function₂[V] subst L via substsGraph L :=
  (construction L).result_defined

instance subst.definable : 𝚺ᴬ₁-Function₂[V] subst L := subst.defined.to_definable

instance subst.definable' (Γ m) : Γᴬ-[m + 1]-Function₂[V] subst L := subst.definable.of_sigmaOne

attribute [irreducible] substsGraph

end

variable {m w : V}

@[simp] lemma substs_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^relk R v) = ^rel k R (termSubstVec L k w v) := by simp [subst, hR, hv, construction]

@[simp] lemma substs_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^nrelk R v) = ^nrel k R (termSubstVec L k w v) := by
  simp [subst, hR, hv, construction]

@[simp] lemma substs_verum (w : V) : subst L w ^⊤ = ^⊤ := by simp [subst, construction]

@[simp] lemma substs_falsum (w : V) : subst L w ^⊥ = ^⊥ := by simp [subst, construction]

@[simp] lemma substs_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋏ q) = subst L w p ^⋏ subst L w q := by simp [subst, hp, hq, construction]

@[simp] lemma substs_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋎ q) = subst L w p ^⋎ subst L w q := by simp [subst, hp, hq, construction]

@[simp] lemma substs_all {p} (hp : IsUFormula L p) :
    subst L w (^∀ p) = ^∀ (subst L (qVec L w) p) := by simp [subst, hp, construction]

@[simp] lemma substs_ex {p} (hp : IsUFormula L p) :
    subst L w (^∃ p) = ^∃ (subst L (qVec L w) p) := by simp [subst, hp, construction]

lemma isUFormula_subst_ISigma1.sigma1_succ_induction {P : V → V → V → Prop} (hP : 𝚺ᴬ₁-Relation₃ P)
    (hRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v →
        P w (^rel k R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v →
        P w (^nrel k R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ w, P w ^⊤ ^⊤)
    (hfalsum : ∀ w, P w ^⊥ ^⊥)
    (hand : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (subst L w p) → P w q (subst L w q) → P w (p ^⋏ q) (subst L w p ^⋏ subst L w q))
    (hor : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (subst L w p) → P w q (subst L w q) → P w (p ^⋎ q) (subst L w p ^⋎ subst L w q))
    (hall : ∀ w p, IsUFormula L p → P (qVec L w) p (subst L (qVec L w) p) →
        P w (^∀ p) (^∀ (subst L (qVec L w) p)))
    (hexs : ∀ w p, IsUFormula L p → P (qVec L w) p (subst L (qVec L w) p) →
        P w (^∃ p) (^∃ (subst L (qVec L w) p))) :
    ∀ {w p}, IsUFormula L p → P w p (subst L w p) := by
  suffices ∀ param p, IsUFormula L p → P param p ((construction L).result L param p) by
    intro w p hp; simpa using! this w p hp
  apply (construction L).uformula_result_induction (P := fun param p y ↦ P param p y)
  · definability
  · intro param k R v hkR hv; simpa using! hRel param k R v hkR hv
  · intro param k R v hkR hv; simpa using! hNRel param k R v hkR hv
  · intro param; simpa using! hverum param
  · intro param; simpa using! hfalsum param
  · intro param p q hp hq ihp ihq
    simpa [subst] using!
      hand param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro param p q hp hq ihp ihq
    simpa [subst] using!
      hor param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro param p hp ihp
    change P param (^∀ p) (subst L param (^∀ p))
    simpa [hp] using hall param p hp (ihp 0 (by simp [construction]))
  · intro param p hp ihp
    change P param (^∃ p) (subst L param (^∃ p))
    simpa [hp] using hexs param p hp (ihp 0 (by simp [construction]))

lemma semiformula_subst_induction {P : V → V → V → V → Prop} (hP : 𝚺ᴬ₁-Relation₄ P)
    (hRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v →
        P n w (^rel k R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v →
        P n w (^nrel k R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ n w, P n w ^⊤ ^⊤)
    (hfalsum : ∀ n w, P n w ^⊥ ^⊥)
    (hand : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (subst L w p) → P n w q (subst L w q) → P n w (p ^⋏ q) (subst L w p ^⋏ subst L w q))
    (hor : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (subst L w p) → P n w q (subst L w q) → P n w (p ^⋎ q) (subst L w p ^⋎ subst L w q))
    (hall : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (subst L (qVec L w) p) → P n w (^∀ p) (^∀ (subst L (qVec L w) p)))
    (hexs : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (subst L (qVec L w) p) → P n w (^∃ p) (^∃ (subst L (qVec L w) p))) :
    ∀ {n p w}, IsSemiformula L n p → P n w p (subst L w p) := by
  suffices ∀ param n p, IsSemiformula L n p → P n param p ((construction L).result L param p) by
    intro n p w hp; simpa using! this w n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n param p y)
  · definability
  · intro n param k R v hkR hv; simpa using! hRel n param k R v hkR hv
  · intro n param k R v hkR hv; simpa using! hNRel n param k R v hkR hv
  · intro n param; simpa using! hverum n param
  · intro n param; simpa using! hfalsum n param
  · intro n param p q hp hq ihp ihq
    simpa [subst] using!
      hand n param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro n param p q hp hq ihp ihq
    simpa [subst] using!
      hor n param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro n param p hp ihp
    change P n param (^∀ p) (subst L param (^∀ p))
    simpa [hp.isUFormula] using hall n param p hp (ihp 0 (by simp [construction]))
  · intro n param p hp ihp
    change P n param (^∃ p) (subst L param (^∃ p))
    simpa [hp.isUFormula] using hexs n param p hp (ihp 0 (by simp [construction]))

@[simp] lemma IsSemiformula.subst {n p m w : V} :
    IsSemiformula L n p → IsSemitermVec L n m w → IsSemiformula L m (subst L w p) := by
  let fw : V → V → V → V → V := fun _ w _ _ ↦ Max.max w (qVec L w)
  have hfw : 𝚺ᴬ₁-Function₄ fw := by definability
  let fn : V → V → V → V → V := fun _ _ n _ ↦ n + 1
  have hfn : 𝚺ᴬ₁-Function₄ fn := by definability
  let fm : V → V → V → V → V := fun _ _ _ m ↦ m + 1
  have hfm : 𝚺ᴬ₁-Function₄ fm := by definability
  apply bounded_all_sigma1_order_induction₃ hfw hfn hfm ?_ ?_ p w n m
  · definability
  intro p w n m ih hp hw
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
        ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp
  · simp
  · have ih₁ : IsSemiformula L m (Bootstrapping.subst L w p₁) :=
      ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Bootstrapping.subst L w p₂) :=
      ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : IsSemiformula L m (Bootstrapping.subst L w p₁) :=
      ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Bootstrapping.subst L w p₂) :=
      ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn])
      (m + 1) (by simp [fm]) h₁ hw.qVec
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn])
      (m + 1) (by simp [fm]) h₁ hw.qVec

lemma substs_not_uformula {w x : V} (h : ¬IsUFormula L x) :
    subst L w x = 0 := (construction L).result_prop_not _ h

lemma substs_neg {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → subst L w (neg L p) = neg L (subst L w p) := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intros n k R v hR hv m w hw
    rw [neg_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm,
        neg_rel hR (hw.termSubstVec hv).isUTerm]
  · intros n k R v hR hv m w hw
    rw [neg_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm,
        neg_nrel hR (hw.termSubstVec hv).isUTerm]
  · intros; simp [*]
  · intros; simp [*]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_and hp.isUFormula hq.isUFormula,
      substs_or hp.neg.isUFormula hq.neg.isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      neg_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_or hp.isUFormula hq.isUFormula,
      substs_and hp.neg.isUFormula hq.neg.isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      neg_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [neg_all hp.isUFormula, substs_ex hp.neg.isUFormula,
      substs_all hp.isUFormula, neg_all (hp.subst hw.qVec).isUFormula, ih hw.qVec]
  · intro n p hp ih m w hw
    rw [neg_ex hp.isUFormula, substs_all hp.neg.isUFormula,
      substs_ex hp.isUFormula, neg_ex (hp.subst hw.qVec).isUFormula, ih hw.qVec]

lemma shift_substs {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → shift L (subst L w p) = subst L (termShiftVec L n w) (shift L p) := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [substs_rel hR hv.isUTerm,
      shift_rel hR (hw.termSubstVec hv).isUTerm,
      shift_rel hR hv.isUTerm,
      substs_rel hR hv.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n k R v hR hv m w hw
    rw [substs_nrel hR hv.isUTerm,
      shift_nrel hR (hw.termSubstVec hv).isUTerm,
      shift_nrel hR hv.isUTerm,
      substs_nrel hR hv.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n w hw; simp
  · intro n w hw; simp
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      shift_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      shift_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [substs_all hp.isUFormula,
      shift_all (hp.subst hw.qVec).isUFormula,
      shift_all hp.isUFormula,
      substs_all hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]
  · intro n p hp ih m w hw
    rw [substs_ex hp.isUFormula,
      shift_exs (hp.subst hw.qVec).isUFormula,
      shift_exs hp.isUFormula,
      substs_ex hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]

lemma substs_substs {p} (hp : IsSemiformula L l p) :
    IsSemitermVec L n m w → IsSemitermVec L l n v → subst L w (subst L v p) =
        subst L (termSubstVec L l w v) p := by
  revert m w n v
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_rel hR hts.isUTerm,
      substs_rel hR (hv.termSubstVec hts).isUTerm,
      substs_rel hR hts.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm])
        (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_nrel hR hts.isUTerm,
      substs_nrel hR (hv.termSubstVec hts).isUTerm,
      substs_nrel hR hts.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm])
        (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intros; simp
  · intros; simp
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_and hp.isUFormula hq.isUFormula,
      substs_and (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_or hp.isUFormula hq.isUFormula,
      substs_or (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p hp ih m w n v hw hv
    rw [substs_all hp.isUFormula,
      substs_all (hp.subst hv.qVec).isUFormula,
      substs_all hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]
  · intro l p hp ih m w n v hw hv
    rw [substs_ex hp.isUFormula,
      substs_ex (hp.subst hv.qVec).isUFormula,
      substs_ex hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]

lemma subst_eq_self {n w : V} (hp : IsSemiformula L n p) (hw : IsSemitermVec L n n w)
    (H : ∀ i < n, w.[i] = ^#i) :
    subst L w p = p := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]

lemma subst_eq_self₁ (hp : IsSemiformula L 1 p) :
    subst L (^#0 ∷ 0) p = p := subst_eq_self hp (by simp) (by simp)

end subst

variable (L)

noncomputable def substs1 (t u : V) : V := subst L ?[t] u

noncomputable def substs1Graph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “ z t p. ∃ v, !adjoinDef v t 0 ∧ !(substsGraph L) z v p”

variable {L}

section substs1

section

instance substs1.defined : 𝚺ᴬ₁-Function₂[V] substs1 L via substs1Graph L :=
  .mk fun v ↦ by simp [substs1Graph]; rfl

instance substs1.definable : 𝚺ᴬ₁-Function₂[V] substs1 L := substs1.defined.to_definable

instance substs1.definable' (Γ m) : Γᴬ-[m + 1]-Function₂[V] substs1 L :=
  substs1.definable.of_sigmaOne

end

lemma IsSemiformula.substs1 {n t p : V} (ht : IsSemiterm L n t) (hp : IsSemiformula L 1 p) :
    IsSemiformula L n (substs1 L t p) :=
  IsSemiformula.subst hp (by simp [ht])

end substs1

variable (L)

noncomputable def free (p : V) : V := substs1 L ^&0 (shift L p)

noncomputable def freeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “q p. ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !(shiftGraph L) sp p ∧ !(substs1Graph L) q fz sp”

variable {L}

/-! ### free function -/

section free

section

instance free.defined : 𝚺ᴬ₁-Function₁[V] free L via freeGraph L :=
  .mk fun v ↦ by simp [freeGraph, free]

instance free.definable : 𝚺ᴬ₁-Function₁[V] free L := free.defined.to_definable

instance free.definable' (Γ m) : Γᴬ-[m + 1]-Function₁[V] free L := free.definable.of_sigmaOne

end

@[simp] lemma IsSemiformula.free {p : V} (hp : IsSemiformula L 1 p) : IsFormula L (free L p) :=
  IsSemiformula.substs1 (by simp) hp.shift

end free

section free1

variable (L)

noncomputable def free1 (p : V) : V := subst L ?[^&0, ^#0] (shift L p)

variable {L}

@[simp] lemma IsSemiformula.free1 {p : V} (hp : IsSemiformula L 2 p) :
    IsSemiformula L 1 (free1 L p) :=
  IsSemiformula.subst (m := 1) hp.shift
      (SemitermVec.adjoin (SemitermVec.adjoin (IsSemitermVec.empty _) (by simp)) (by simp))

end free1

/-! ### Complexity of formula -/

section complexity

namespace FormulaComplexity

def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. y = 0”
  nrel := .mkSigma “y param k R v. y = 0”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y (y₁ + 1) (y₂ + 1)”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y (y₁ + 1) (y₂ + 1)”
  all := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁ + 1”
  exs := .mkSigma “y param p₁ ys. ∃ y₁, !nthDef y₁ ys 0 ∧ y = y₁ + 1”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun k R v ↦ 0
  nrel {_} := fun k R v ↦ 0
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ max y₁ y₂ + 1
  or {_} := fun _ _ y₁ y₂ ↦ max y₁ y₂ + 1
  all {_} := fun _ ys ↦ ys.[0] + 1
  exs {_} := fun _ ys ↦ ys.[0] + 1
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  or_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end FormulaComplexity

open FormulaComplexity

variable (L)

noncomputable def formulaComplexity (p : V) : V := construction.result L 0 p

noncomputable def formulaComplexityGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (blueprint.result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

section

instance formulaComplexity.defined :
    𝚺ᴬ₁-Function₁[V] formulaComplexity L via formulaComplexityGraph L := .mk fun v ↦ by
  simpa [formulaComplexityGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! construction.result_defined.defined ![v 0, 0, v 1]

instance formulaComplexity.definable : 𝚺ᴬ₁-Function₁[V] formulaComplexity L :=
  formulaComplexity.defined.to_definable

instance formulaComplexity.definable' (Γ m) : Γᴬ-[m + 1]-Function₁[V] formulaComplexity L :=
  .of_sigmaOne formulaComplexity.definable

end

@[simp] lemma formulaComplexity_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^rel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]

@[simp] lemma formulaComplexity_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^nrel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]

@[simp] lemma formulaComplexity_verum :
    formulaComplexity L (^⊤ : V) = 0 := by simp [formulaComplexity, construction]

@[simp] lemma formulaComplexity_falsum :
    formulaComplexity L (^⊥ : V) = 0 := by simp [formulaComplexity, construction]

@[simp] lemma formulaComplexity_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋏ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by
  simp [formulaComplexity, hp, hq, construction]

@[simp] lemma formulaComplexity_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋎ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by
  simp [formulaComplexity, hp, hq, construction]

@[simp] lemma formulaComplexity_all {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∀ p) = formulaComplexity L p + 1 := by
  simp [formulaComplexity, hp, construction]

@[simp] lemma formulaComplexity_ex {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∃ p) = formulaComplexity L p + 1 := by
  simp [formulaComplexity, hp, construction]

lemma formulaComplexity_not_uformula {x : V} (h : ¬IsUFormula L x) :
    formulaComplexity L x = 0 := construction.result_prop_not _ h

@[simp] lemma formulaComplexity_neg {p : V} :
    IsUFormula L p → formulaComplexity L (neg L p) = formulaComplexity L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma formulaComplexity_shift {p : V} :
    IsUFormula L p → formulaComplexity L (shift L p) = formulaComplexity L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma fomulaComplexity_substs {n p : V} (hp : IsSemiformula L n p) {m w : V} :
    IsSemitermVec L n m w → formulaComplexity L (subst L w p) = formulaComplexity L p := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [formulaComplexity_rel hR hv.isUTerm, substs_rel hR hv.isUTerm,
        formulaComplexity_rel hR (hw.termSubstVec hv).isUTerm]
  · intro n k R v hR hv m w hw
    rw [formulaComplexity_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm,
        formulaComplexity_nrel hR (hw.termSubstVec hv).isUTerm]
  · intro n m w hw
    rw [substs_verum]
  · intro n m w hw
    rw [substs_falsum]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      formulaComplexity_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw,
      formulaComplexity_and hp.isUFormula hq.isUFormula]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      formulaComplexity_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw,
      formulaComplexity_or hp.isUFormula hq.isUFormula]
  · intro n p hp ihp m w hw
    rw [substs_all hp.isUFormula,
     formulaComplexity_all (hp.subst hw.qVec).isUFormula,
     ihp (hw.qVec),
     formulaComplexity_all hp.isUFormula]
  · intro n p hp ihp m w hw
    rw [substs_ex hp.isUFormula,
     formulaComplexity_ex (hp.subst hw.qVec).isUFormula,
     ihp (hw.qVec),
     formulaComplexity_ex hp.isUFormula]

lemma fomulaComplexity_substs1 {p : V} (hp : IsSemiformula L 1 p) {m t : V}
    (ht : IsSemiterm L m t) :
    formulaComplexity L (substs1 L t p) = formulaComplexity L p := by
  unfold substs1
  rw [fomulaComplexity_substs hp (IsSemitermVec.singleton.mpr ht)]


lemma fomulaComplexity_free {p : V} (hp : IsSemiformula L 1 p) :
    formulaComplexity L (free L p) = formulaComplexity L p := by
  unfold free
  have : IsSemiterm (V := V) L 0 ^&0 := by simp
  rw [fomulaComplexity_substs1 hp.shift this,
    formulaComplexity_shift hp.isUFormula]

lemma fomulaComplexity_free1 {p : V} (hp : IsSemiformula L 2 p) :
    formulaComplexity L (free1 L p) = formulaComplexity L p := by
  unfold free1
  have : IsSemiterm (V := V) L 0 ^&0 := by simp
  rw [fomulaComplexity_substs (m := 1) (V := V) hp.shift]
  · rw [formulaComplexity_shift hp.isUFormula]
  · apply IsSemitermVec.adjoin ?_ (by simp)
    apply IsSemitermVec.adjoin ?_ (by simp)
    exact IsSemitermVec.nil _

end complexity

@[simp] lemma lt_max_succ_left (a b : V) : a < max a b + 1 := lt_succ_iff_le.mpr <| by simp

@[simp] lemma lt_max_succ_right (a b : V) : b < max a b + 1 := lt_succ_iff_le.mpr <| by simp

/-! A structural induction correspondence to `FFL.FirstOrder.Semiformula.formulaRec`.  -/
lemma IsFormula.sigma1_structural_induction {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsFormula L p → IsFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsFormula L p → IsFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 1 p → P (free L p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 1 p → P (free L p) → P (^∃ p)) {p} :
    IsFormula L p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free L (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 1 p₁ := by simpa using h₁
    have : P (free L p₁) := ih (free L p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by simp [fomulaComplexity_free h₁, h₁.isUFormula])
      (h₁.free)
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 1 p₁ := by simpa using h₁
    have : P (free L p₁) := ih (free L p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by simp [fomulaComplexity_free h₁, h₁.isUFormula])
      (h₁.free)
    exact hexs _ h₁ this

lemma IsFormula.sigma1_structural_induction₂ {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p → P (free1 L p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p → P (free1 L p) → P (^∃ p)) {p} :
    IsSemiformula L 1 p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free1 L (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L p₁) := ih (free1 L p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by simp [fomulaComplexity_free1 h₁, h₁.isUFormula])
      h₁.free1
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa  [one_add_one_eq_two] using h₁
    have : P (free1 L p₁) := ih (free1 L p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by simp [fomulaComplexity_free1 h₁, h₁.isUFormula])
      h₁.free1
    exact hexs _ h₁ this

lemma IsFormula.sigma1_structural_induction₂_ss {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p → P (free1 L <| shift L <| shift L <| p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p → P (free1 L <| shift L <| shift L <| p) → P (^∃ p)) {p} :
    IsSemiformula L 1 p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free1 L <| shift L <| shift L <| (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L <| shift L <| shift L <| p₁) :=
      ih (free1 L <| shift L <| shift L <| p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by rw [fomulaComplexity_free1 h₁.shift.shift, formulaComplexity_shift h₁.shift.isUFormula,
          formulaComplexity_shift h₁.isUFormula]; simp [h₁.isUFormula])
      h₁.shift.shift.free1
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L <| shift L <| shift L <| p₁) :=
      ih (free1 L <| shift L <| shift L <| p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by rw [fomulaComplexity_free1 h₁.shift.shift, formulaComplexity_shift h₁.shift.isUFormula,
          formulaComplexity_shift h₁.isUFormula]; simp [h₁.isUFormula])
      h₁.shift.shift.free1
    exact hexs _ h₁ this

/-
section fvfree

variable (L)

def Language.IsFVFree (n p : V) : Prop := IsSemiformula L n p ∧ shift L p = p

section

def _root_.FFL.FirstOrder.Arithmetic.LDef.isFVFreeDef (pL : LDef) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “n p | !(isSemiformula L).sigma n p ∧ !pshift LDef p p”

lemma isFVFree_defined : 𝚺ᴬ₁-Relation L.IsFVFree via pL.isFVFreeDef := by
  intro v; simp [LDef.isFVFreeDef, Bounding.HierarchySymbol.Semiformula.val_sigma,
    (semiformula_defined L).df.iff, (shift_defined L).df.iff]
  simp [Language.IsFVFree, eq_comm]

end

variable {L}

@[simp] lemma Language.IsFVFree.verum (n : V) : L.IsFVFree n ^⊤[n] := by simp [Language.IsFVFree]

@[simp] lemma Language.IsFVFree.falsum (n : V) : L.IsFVFree n ^⊥[n] := by simp [Language.IsFVFree]

lemma Language.IsFVFree.and {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋏[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.or {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋎[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.all {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∀¹[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

lemma Language.IsFVFree.exs {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∃¹[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

@[simp] lemma Language.IsFVFree.neg_iff : L.IsFVFree n (neg L p) ↔ L.IsFVFree n p := by
  constructor
  · intro h
    have hp : Semiformula L n p := IsSemiformula.neg_iff.mp h.1
    have : shift L (neg L p) = neg L p := h.2
    simp [shift_neg hp, neg_inj_iff hp.shift hp] at this
    exact ⟨hp, this⟩
  · intro h; exact ⟨by simp [h.1], by rw [shift_neg h.1, h.2]⟩

end fvfree
-/

namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Arithmetic`).
set_option linter.dupNamespace false

noncomputable def qqEQ (x y : V) : V := ^rel 2 (eqIndex : V) ?[x, y]

noncomputable def qqNEQ (x y : V) : V := ^nrel 2 (eqIndex : V) ?[x, y]

noncomputable def qqLT (x y : V) : V := ^rel 2 (ltIndex : V) ?[x, y]

noncomputable def qqNLT (x y : V) : V := ^nrel 2 (ltIndex : V) ?[x, y]

notation:75 x:75 " ^= " y:76 => qqEQ x y

notation:75 x:75 " ^≠ " y:76 => qqNEQ x y

notation:78 x:78 " ^< " y:79 => qqLT x y

notation:78 x:78 " ^≮ " y:79 => qqNLT x y

@[simp] lemma lt_qqEQ_left (x y : V) : x < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqEQ_right (x y : V) : y < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_left (x y : V) : x < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_right (x y : V) : y < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_left (x y : V) : x < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_right (x y : V) : y < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_left (x y : V) : x < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_right (x y : V) : y < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

def _root_.FFL.FirstOrder.Arithmetic.qqEQDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑eqIndex v”

def _root_.FFL.FirstOrder.Arithmetic.qqNEQDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑eqIndex v”

def _root_.FFL.FirstOrder.Arithmetic.qqLTDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑ltIndex v”

def _root_.FFL.FirstOrder.Arithmetic.qqNLTDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑ltIndex v”

instance qqEQ_defined : 𝚺ᴬ₁-Function₂ (qqEQ : V → V → V) via qqEQDef :=
  .mk fun v ↦ by simp [qqEQDef, numeral_eq_natCast, qqEQ]

instance qqNEQ_defined : 𝚺ᴬ₁-Function₂ (qqNEQ : V → V → V) via qqNEQDef :=
  .mk fun v ↦ by simp [qqNEQDef, numeral_eq_natCast, qqNEQ]

instance qqLT_defined : 𝚺ᴬ₁-Function₂ (qqLT : V → V → V) via qqLTDef :=
  .mk fun v ↦ by simp [qqLTDef, numeral_eq_natCast, qqLT]

instance qqNLT_defined : 𝚺ᴬ₁-Function₂ (qqNLT : V → V → V) via qqNLTDef :=
  .mk fun v ↦ by simp [qqNLTDef, numeral_eq_natCast, qqNLT]

instance (Γ m) : Γᴬ-[m + 1]-Function₂ (qqEQ : V → V → V) := .of_sigmaOne qqEQ_defined.to_definable

instance (Γ m) : Γᴬ-[m + 1]-Function₂ (qqNEQ : V → V → V) := .of_sigmaOne qqNEQ_defined.to_definable

instance (Γ m) : Γᴬ-[m + 1]-Function₂ (qqLT : V → V → V) := .of_sigmaOne qqLT_defined.to_definable

instance (Γ m) : Γᴬ-[m + 1]-Function₂ (qqNLT : V → V → V) := .of_sigmaOne qqNLT_defined.to_definable

lemma neg_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^= u) = t ^≠ u := by
  simp only [qqEQ, qqNEQ]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_neq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≠ u) = t ^= u := by
  simp only [qqNEQ, qqEQ]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_lt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^< u) = t ^≮ u := by
  simp only [qqLT, qqNLT]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_nlt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≮ u) = t ^< u := by
  simp only [qqNLT, qqLT]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma substs_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    subst ℒₒᵣ w (t ^= u) = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp only [qqEQ]
  rw [substs_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]
  simp [termSubstVec_cons₂ ht hu]

end Arithmetic

/-! ### Bounded universal quantifier -/

section qqBall

/-- `qqBall u q = ^∀ ((^#0 ^≮ u) ^⋎ q)`, the code of `∀¹[“#0 < u”] q`. -/
noncomputable def qqBall (u q : V) : V := qqAll (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q)

@[simp] lemma lt_q_qqBall (u q : V) : q < qqBall u q :=
  lt_trans (lt_or_right _ _) (lt_forall _)

@[simp] lemma lt_u_qqBall (u q : V) : u < qqBall u q :=
  lt_trans (Arithmetic.lt_qqNLT_right _ _) (lt_trans (lt_or_left _ _) (lt_forall _))

def _root_.FFL.FirstOrder.Arithmetic.qqBallDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ nlt, !qqNLTDef nlt bv u ∧ ∃ g, !qqOrDef g nlt q ∧ !qqAllDef p g”

instance qqBall_defined :
    𝚺ᴬ₁-Function₂ (qqBall : V → V → V) via Arithmetic.qqBallDef := .mk fun v ↦ by
  simp [Arithmetic.qqBallDef, qqBall, (Arithmetic.qqNLT_defined (V := V)).df]

instance qqBall_definable (Γ m) : Γᴬ-[m + 1]-Function₂ (qqBall : V → V → V) :=
  .of_sigmaOne qqBall_defined.to_definable

end qqBall

end FFL.FirstOrder.Arithmetic.Bootstrapping
