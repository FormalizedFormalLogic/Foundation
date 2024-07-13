import Arithmetization.ISigmaOne.HFS.Fixpoint

/-!

# Vec

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

section cons

instance : Cons V V := ⟨(⟪·, ·⟫ + 1)⟩

scoped infixr:67 " ∷ " => cons

syntax "?[" term,* "]" : term

macro_rules
  | `(?[$term:term, $terms:term,*]) => `(cons $term ?[$terms,*])
  | `(?[$term:term]) => `(cons $term 0)
  | `(?[]) => `(0)

@[app_unexpander Cons.cons]
def consUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ?[$terms,*]) => `(?[$term, $terms,*])
  | `($_ $term 0) => `(?[$term])
  | _ => throw ()

lemma cons_def (x v : V) : x ∷ v = ⟪x, v⟫ + 1 := rfl

@[simp] lemma fstIdx_cons (x v : V) : fstIdx (x ∷ v) = x := by simp [cons_def, fstIdx]

@[simp] lemma sndIdx_cons (x v : V) : sndIdx (x ∷ v) = v := by simp [cons_def, sndIdx]

lemma succ_eq_cons (x : V) : x + 1 = π₁ x ∷ π₂ x := by simp [cons_def]

@[simp] lemma lt_cons (x v : V) : x < x ∷ v := by simp [cons_def, lt_succ_iff_le]

@[simp] lemma lt_cons' (x v : V) : v < x ∷ v := by simp [cons_def, lt_succ_iff_le]

@[simp] lemma zero_lt_cons (x v : V) : 0 < x ∷ v := by simp [cons_def]

@[simp] lemma cons_ne_zero (x v : V) : x ∷ v ≠ 0 := by simp [cons_def]

@[simp] lemma zero_ne_cons (x v : V) : 0 ≠ x ∷ v := by symm; simp [cons_def]

lemma nil_or_cons (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v := by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨π₁ z, π₂ z, by simp [succ_eq_cons]⟩

@[simp] lemma cons_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [cons_def]

lemma cons_le_cons {x₁ x₂ v₁ v₂ : V} (hx : x₁ ≤ x₂) (hv : v₁ ≤ v₂) :
    x₁ ∷ v₁ ≤ x₂ ∷ v₂ := by simpa [cons_def] using pair_le_pair hx hv

end cons

/-!

### N-th element of List

-/

namespace Nth

def Phi (C : Set V) (pr : V) : Prop :=
  (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ ⟪sndIdx v, i, x⟫ ∈ C)

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    (∃ v ≤ pr, ∃ fst ≤ v, fst = fstIdx v ∧ pr = ⟪v, 0, fst⟫) ∨
    (∃ v ≤ pr, ∃ i ≤ pr, ∃ x ≤ pr, pr = ⟪v, i + 1, x⟫ ∧ ∃ snd ≤ v, snd = sndIdx v ∧ ∃ six < C, six = ⟪snd, i, x⟫ ∧ six ∈ C) := by
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, i, x, rfl, hC⟩)
    · left; exact ⟨v, by simp, _, by simp, rfl, rfl⟩
    · right; exact ⟨v, by simp,
        i, le_trans (le_trans (by simp) (le_pair_left _ _)) (le_pair_right _ _),
        x, le_trans (by simp) (le_pair_right _ _), rfl, _, by simp, rfl, _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨v, _, _, _, rfl, rfl⟩ | ⟨v, _, i, _, x, _, rfl, _, _, rfl, _, _, rfl, hC⟩)
    · left; exact ⟨v, rfl⟩
    · right; exact ⟨v, i, x, rfl, hC⟩

def blueprint : Fixpoint.Blueprint 0 where
  core := .ofZero
    (.mkSigma “pr C |
    (∃ v <⁺ pr, ∃ fst <⁺ v, !fstIdxDef fst v ∧ !pair₃Def pr v 0 fst) ∨
    (∃ v <⁺ pr, ∃ i <⁺ pr, ∃ x <⁺ pr, !pair₃Def pr v (i + 1) x ∧
      ∃ snd <⁺ v, !sndIdxDef snd v ∧ ∃ six < C, !pair₃Def six snd i x ∧ six ∈ C)”
    (by simp))
    _

def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| by intro v; simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, x, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, x, rfl, hC h⟩

instance : construction.Finite V where
  finite := by
    rintro C v x (h | ⟨v, i, x, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪sndIdx v, i, x⟫ + 1, Or.inr ⟨v, i, x, rfl, h, by simp⟩⟩

def Graph : V → Prop := construction.Fixpoint ![]

section

def graphDef : 𝚺₁-Semisentence 1 := blueprint.fixpointDef

lemma graph_defined : 𝚺₁-Predicate (Graph : V → Prop) via graphDef :=
  construction.fixpoint_defined

instance graph_definable : 𝚺₁-Predicate (Graph : V → Prop) := Defined.to_definable _ graph_defined

end

/-- TODO: move-/
@[simp] lemma zero_ne_add_one (x : V) : 0 ≠ x + 1 := ne_of_lt (by simp)

lemma graph_case {pr : V} :
    Graph pr ↔
    (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ Graph ⟪sndIdx v, i, x⟫) :=
  construction.case

lemma graph_zero {v x : V} :
    Graph ⟪v, 0, x⟫ ↔ x = fstIdx v := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨v, h⟩ | ⟨v, i, x, h, _⟩)
    · simp at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl
    · simp at h
  · rintro rfl; exact graph_case.mpr <| Or.inl ⟨v, rfl⟩

lemma graph_succ {v i x : V} :
    Graph ⟪v, i + 1, x⟫ ↔ Graph ⟪sndIdx v, i, x⟫ := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨v, h⟩ | ⟨v, i, x, h, hv⟩)
    · simp at h
    · simp at h; rcases h with ⟨rfl, rfl, rfl⟩; exact hv
  · intro h; exact graph_case.mpr <| Or.inr ⟨v, i, x, rfl, h⟩

lemma graph_exists (v i : V) : ∃ x, Graph ⟪v, i, x⟫ := by
  suffices ∀ i' ≤ i, ∀ v' ≤ v, ∃ x, Graph ⟪v', i', x⟫ from this i (by simp) v (by simp)
  intro i' hi'
  induction i' using induction_iSigmaOne
  · definability
  case zero =>
    intro v' _
    exact ⟨fstIdx v', graph_case.mpr <| Or.inl ⟨v', rfl⟩⟩
  case succ i' ih =>
    intro v' hv'
    rcases ih (le_trans le_self_add hi') (sndIdx v') (le_trans (by simp) hv') with ⟨x, hx⟩
    exact ⟨x, graph_case.mpr <| Or.inr ⟨v', i', x, rfl, hx⟩⟩

lemma graph_unique {v i x₁ x₂ : V} : Graph ⟪v, i, x₁⟫ → Graph ⟪v, i, x₂⟫ → x₁ = x₂ := by
  induction i using induction_iPiOne generalizing v x₁ x₂
  · definability
  case zero =>
    simp [graph_zero]
    rintro rfl rfl; rfl
  case succ i ih =>
    simp [graph_succ]
    exact ih

lemma graph_existsUnique (v i : V) : ∃! x, Graph ⟪v, i, x⟫ := by
  rcases graph_exists v i with ⟨x, hx⟩
  exact ExistsUnique.intro x hx (fun y hy ↦ graph_unique hy hx)

end Nth

section nth

open Nth

def nth (v i : V) : V := Classical.choose! (graph_existsUnique v i)

scoped notation:max v:max ".[" i "]" => nth v i

lemma nth_graph (v i : V) : Graph ⟪v, i, v.[i]⟫ :=
  Classical.choose!_spec (graph_existsUnique v i)

lemma nth_eq_of_graph {v i x : V} (h : Graph ⟪v, i, x⟫) : nth v i = x := graph_unique (nth_graph v i) h

lemma nth_zero (v : V) : v.[0] = fstIdx v := nth_eq_of_graph (graph_zero.mpr rfl)

lemma nth_succ (v i : V) : v.[i + 1] = (sndIdx v).[i] := nth_eq_of_graph (graph_succ.mpr <| nth_graph _ _)

@[simp] lemma nth_cons_zero (x v : V) : (x ∷ v).[0] = x := by
  simp [nth_zero]

@[simp] lemma nth_cons_succ (x v i : V) : (x ∷ v).[i + 1] = v.[i] := by
  simp [nth_succ]

@[simp] lemma nth_cons_one (x v : V) : (x ∷ v).[1] = v.[0] := by
  simpa using nth_cons_succ x v 0

@[simp] lemma nth_cons_two (x v : V) : (x ∷ v).[2] = v.[1] := by
  simpa [-nth_cons_succ, one_add_one_eq_two] using nth_cons_succ x v 1

lemma cons_induction (Γ) {P : V → Prop} (hP : (Γ, 1)-Predicate P)
    (nil : P 0) (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  order_induction_hh ℒₒᵣ Γ 1 hP (by
    intro v ih
    rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩)
    · exact nil
    · exact cons _ _ (ih v (by simp)))

@[elab_as_elim]
lemma cons_induction_sigma₁ {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (nil : P 0) (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  cons_induction 𝚺 hP nil cons

@[elab_as_elim]
lemma cons_induction_pi₁ {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (nil : P 0) (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  cons_induction 𝚷 hP nil cons

section

def _root_.LO.FirstOrder.Arith.nthDef : 𝚺₁-Semisentence 3 :=
  .mkSigma “y v i | ∃ pr, !pair₃Def pr v i y ∧ !graphDef pr” (by simp)

lemma nth_defined : 𝚺₁-Function₂ (nth : V → V → V) via nthDef := by
  intro v; simp [nthDef, graph_defined.df.iff]
  constructor
  · intro h; rw [h]; exact nth_graph _ _
  · intro h; simp [nth_eq_of_graph h]

@[simp] lemma eval_nthDef (v) :
    Semiformula.Evalbm V v nthDef.val ↔ v 0 = nth (v 1) (v 2) := nth_defined.df.iff v

instance nth_definable : 𝚺₁-Function₂ (nth : V → V → V) := Defined.to_definable _ nth_defined

instance nth_definable' (Γ) : (Γ, m + 1)-Function₂ (nth : V → V → V) := .of_sigmaOne nth_definable _ _

def _root_.LO.FirstOrder.Arith.consDef : 𝚺₀-Semisentence 3 :=
  .mkSigma “w x v | ∃ xv < w, !pairDef xv x v ∧ w = xv + 1” (by simp)

lemma cons_defined : 𝚺₀-Function₂ (cons : V → V → V) via consDef := by
  intro v; simp [consDef]
  constructor
  · intro h; rw [h]; exact ⟨_, by simp [cons_def], rfl, rfl⟩
  · intro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_cons (v) :
    Semiformula.Evalbm V v consDef.val ↔ v 0 = v 1 ∷ v 2 := cons_defined.df.iff v

instance cons_definable : 𝚺₀-Function₂ (cons : V → V → V) := Defined.to_definable _ cons_defined

instance cons_definable' (Γ) : Γ-Function₂ (cons : V → V → V) := .of_zero cons_definable _

def _root_.LO.FirstOrder.Arith.mkVec₁Def : 𝚺₀-Semisentence 2 := .mkSigma
  “s x | !consDef s x 0” (by simp)

lemma mkVec₁_defined : 𝚺₀-Function₁ (fun x : V ↦ ?[x]) via mkVec₁Def := by
  intro v; simp [mkVec₁Def]

@[simp] lemma eval_mkVec₁Def (v) :
    Semiformula.Evalbm V v mkVec₁Def.val ↔ v 0 = ?[v 1] := mkVec₁_defined.df.iff v

instance mkVec₁_definable : 𝚺₀-Function₁ (fun x : V ↦ ?[x]) := Defined.to_definable _ mkVec₁_defined

instance mkVec₁_definable' (Γ) : Γ-Function₁ (fun x : V ↦ ?[x]) := .of_zero mkVec₁_definable _

def _root_.LO.FirstOrder.Arith.mkVec₂Def : 𝚺₁-Semisentence 3 := .mkSigma
  “s x y | ∃ sy, !mkVec₁Def sy y ∧ !consDef s x sy” (by simp)

lemma mkVec₂_defined : 𝚺₁-Function₂ (fun x y : V ↦ ?[x, y]) via mkVec₂Def := by
  intro v; simp [mkVec₂Def]

@[simp] lemma eval_mkVec₂Def (v) :
    Semiformula.Evalbm V v mkVec₂Def.val ↔ v 0 = ?[v 1, v 2] := mkVec₂_defined.df.iff v

instance mkVec₂_definable : 𝚺₁-Function₂ (fun x y : V ↦ ?[x, y]) := Defined.to_definable _ mkVec₂_defined

instance mkVec₂_definable' (Γ) : (Γ, m + 1)-Function₂ (fun x y : V ↦ ?[x, y]) := .of_sigmaOne mkVec₂_definable _ _

end

lemma cons_absolute (a v : ℕ) : ((a ∷ v : ℕ) : V) = (a : V) ∷ (v : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V cons_defined cons_defined ![a, v]

/-- TODO: move-/
lemma pi₁_zero : π₁ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₁_le_self 0)

lemma pi₂_zero : π₂ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₂_le_self 0)

@[simp] lemma nth_zero_idx (i : V) : (0).[i] = 0 := by
  induction i using induction_iSigmaOne
  · definability
  case zero => simp [nth_zero, fstIdx, pi₁_zero]
  case succ i ih => simp [nth_succ, sndIdx, pi₂_zero, ih]

lemma nth_lt_of_pos {v} (hv : 0 < v) (i : V) : v.[i] < v := by
  induction i using induction_iPiOne generalizing v
  · definability
  case zero =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · simp [succ_eq_cons]
  case succ i ih =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · simp [succ_eq_cons v]
      rcases eq_zero_or_pos (π₂ v) with (h | h)
      · simp [h]
      · exact lt_trans (ih h) (by simp)

@[simp] lemma nth_le (v i : V) : v.[i] ≤ v := by
  rcases eq_zero_or_pos v with (h | h)
  · simp [h]
  · exact le_of_lt <| nth_lt_of_pos h i

end nth


/-!

### Inductivly Construction of Function on List

-/

namespace VecRec

structure Blueprint (arity : ℕ) where
  nil : 𝚺₁-Semisentence (arity + 1)
  cons : 𝚺₁-Semisentence (arity + 4)

namespace Blueprint

variable {arity : ℕ} (β : Blueprint arity)

def blueprint : Fixpoint.Blueprint arity where
  core := .mkDelta
    (.mkSigma “pr C |
        (∃ nil, !β.nil nil ⋯ ∧ !pairDef pr 0 nil) ∨
        (∃ x < pr, ∃ xs < pr, ∃ ih < C,
          ∃ xxs, !consDef xxs x xs ∧
          ∃ cons, !β.cons cons x xs ih ⋯ ∧
          !pairDef pr xxs cons ∧ :⟪xs, ih⟫:∈ C)”
      (by simp))
    (.mkPi “pr C |
        (∀ nil, !β.nil nil ⋯ → !pairDef pr 0 nil) ∨
        (∃ x < pr, ∃ xs < pr, ∃ ih < C,
          ∀ xxs, !consDef xxs x xs →
          ∀ cons, !β.cons cons x xs ih ⋯ →
          !pairDef pr xxs cons ∧ :⟪xs, ih⟫:∈ C)”
      (by simp))

def graphDef : 𝚺₁-Semisentence (arity + 1) := β.blueprint.fixpointDef

def resultDef : 𝚺₁-Semisentence (arity + 2) :=
  .mkSigma “y xs | ∃ pr, !pairDef pr xs y ∧ !β.graphDef pr ⋯” (by simp)

end Blueprint

variable (V)

structure Construction {arity : ℕ} (β : Blueprint arity) where
  nil (param : Fin arity → V) : V
  cons (param : Fin arity → V) (x xs ih) : V
  nil_defined : DefinedFunction nil β.nil
  cons_defined : DefinedFunction (fun v ↦ cons (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) β.cons

variable {V}

namespace Construction

variable {arity : ℕ} {β : Blueprint arity} (c : Construction V β)

def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  pr = ⟪0, c.nil param⟫ ∨ (∃ x xs ih, pr = ⟪x ∷ xs, c.cons param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C)

private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
    pr = ⟪0, c.nil param⟫ ∨ (∃ x < pr, ∃ xs < pr, ∃ ih < C, pr = ⟪x ∷ xs, c.cons param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C) := by
  constructor
  · rintro (h | ⟨x, xs, ih, rfl, hC⟩)
    · left; exact h
    · right
      exact ⟨x, lt_of_lt_of_le (by simp) (le_pair_left _ _),
        xs, lt_of_lt_of_le (by simp) (le_pair_left _ _), ih, lt_of_mem_rng hC, rfl , hC⟩
  · rintro (h | ⟨x, _, xs, _, ih, _, rfl, hC⟩)
    · left; exact h
    · right; exact ⟨x, xs, ih, rfl, hC⟩

def construction : Fixpoint.Construction V β.blueprint where
  Φ := c.Phi
  defined := ⟨by
    intro v; simp [Blueprint.blueprint, c.nil_defined.df.iff, c.cons_defined.df.iff], by
    intro v; simpa [Blueprint.blueprint, c.nil_defined.df.iff, c.cons_defined.df.iff] using c.phi_iff _ _ _⟩
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, hv, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, hv, rfl, hC h⟩

instance : c.construction.Finite V where
  finite := by
    rintro C v x (h | ⟨x, xs, ih, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪xs, ih⟫ + 1, Or.inr ⟨x, xs, ih, rfl, h, by simp⟩⟩

variable (param : Fin arity → V)

def Graph : V → Prop := c.construction.Fixpoint param

section

lemma graph_defined : Arith.Defined (fun v ↦ c.Graph (v ·.succ) (v 0)) β.graphDef :=
  c.construction.fixpoint_defined

instance graph_definable : Arith.Definable ℒₒᵣ 𝚺₁ (fun v ↦ c.Graph (v ·.succ) (v 0)) := Defined.to_definable _ c.graph_defined

instance graph_definable' (param) : 𝚺₁-Predicate (c.Graph param) := by
  simpa using Definable.retractiont (n := 1) c.graph_definable (#0 :> fun i ↦ &(param i))

end

variable {param}

lemma graph_case {pr : V} :
    c.Graph param pr ↔ pr = ⟪0, c.nil param⟫ ∨ (∃ x xs ih, pr = ⟪x ∷ xs, c.cons param x xs ih⟫ ∧ c.Graph param ⟪xs, ih⟫) :=
  c.construction.case

lemma graph_nil {l : V} :
    c.Graph param ⟪0, l⟫ ↔ l = c.nil param := by
  constructor
  · intro h
    rcases c.graph_case.mp h with (h | ⟨x, xs, ih, h, _⟩)
    · simp at h; rcases h with ⟨rfl, rfl⟩; rfl
    · simp at h
  · rintro rfl; exact c.graph_case.mpr <| Or.inl rfl

lemma graph_cons {x xs y : V} :
    c.Graph param ⟪x ∷ xs, y⟫ ↔ ∃ y', y = c.cons param x xs y' ∧ c.Graph param ⟪xs, y'⟫ := by
  constructor
  · intro h
    rcases c.graph_case.mp h with (h | ⟨x, xs, y, h, hg⟩)
    · simp at h
    · simp at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨y, rfl, hg⟩
  · rintro ⟨y, rfl, h⟩; exact c.graph_case.mpr <| Or.inr ⟨x, xs, y, rfl, h⟩

variable (param)

lemma graph_exists (xs : V) : ∃ y, c.Graph param ⟪xs, y⟫ := by
  induction xs using cons_induction_sigma₁
  · definability
  case nil =>
    exact ⟨c.nil param, c.graph_nil.mpr rfl⟩
  case cons x xs ih =>
    · rcases ih with ⟨y, hy⟩
      exact ⟨c.cons param x xs y, c.graph_cons.mpr ⟨y, rfl, hy⟩⟩

variable {param}

lemma graph_unique {xs y₁ y₂ : V} : c.Graph param ⟪xs, y₁⟫ → c.Graph param ⟪xs, y₂⟫ → y₁ = y₂ := by
  induction xs using cons_induction_pi₁ generalizing y₁ y₂
  · definability
  case nil =>
    simp [graph_nil]; rintro rfl rfl; rfl
  case cons x v ih =>
    simp [graph_cons]
    rintro l₁ rfl h₁ l₂ rfl h₂
    rcases ih h₁ h₂; rfl

variable (param)

lemma graph_existsUnique (xs : V) : ∃! y, c.Graph param ⟪xs, y⟫ := by
  rcases c.graph_exists param xs with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' hy' ↦ c.graph_unique hy' hy)

def result (xs : V) : V := Classical.choose! (c.graph_existsUnique param xs)

lemma result_graph (xs : V) : c.Graph param ⟪xs, c.result param xs⟫ :=
  Classical.choose!_spec (c.graph_existsUnique param xs)

lemma result_eq_of_graph {xs y : V} (h : c.Graph param ⟪xs, y⟫) : c.result param xs = y :=
  c.graph_unique (c.result_graph param xs) h

@[simp] lemma result_nil : c.result param (0 : V) = c.nil param := c.result_eq_of_graph param (c.graph_nil.mpr rfl)

@[simp] lemma result_cons (x xs : V) :
    c.result param (x ∷ xs) = c.cons param x xs (c.result param xs) :=
  c.result_eq_of_graph param (c.graph_cons.mpr ⟨_, rfl, c.result_graph param xs⟩)

section

lemma result_defined : Arith.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.resultDef := by
  intro v; simp [Blueprint.resultDef, c.graph_defined.df.iff]
  constructor
  · intro h; rw [h]; exact c.result_graph _ _
  · intro h; rw [c.result_eq_of_graph _ h]

@[simp] lemma eval_resultDef (v) :
    Semiformula.Evalbm V v β.resultDef.val ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.df.iff v

instance result_definable : Arith.DefinableFunction ℒₒᵣ 𝚺₁ (fun v ↦ c.result (v ·.succ) (v 0)) :=
  Defined.to_definable _ c.result_defined

instance result_definable' (Γ m) :
  Arith.DefinableFunction ℒₒᵣ (Γ, m + 1) (fun v ↦ c.result (v ·.succ) (v 0)) := .of_sigmaOne c.result_definable _ _

end

end Construction

end VecRec

/-!

### Length of List

-/

namespace Len

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y | y = 0” (by simp)
  cons := .mkSigma “y x xs ih | y = ih + 1” (by simp)

def construction : VecRec.Construction V blueprint where
  nil _ := 0
  cons _ _ _ ih := ih + 1
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]; rfl

end Len

section len

open Len

def len (v : V) : V := construction.result ![] v

@[simp] lemma len_nil : len (0 : V) = 0 := by simp [len, construction]

@[simp] lemma len_cons (x v : V) : len (x ∷ v) = len v + 1 := by simp [len, construction]

section

def _root_.LO.FirstOrder.Arith.lenDef : 𝚺₁-Semisentence 2 := blueprint.resultDef

lemma len_defined : 𝚺₁-Function₁ (len : V → V) via lenDef := construction.result_defined

@[simp] lemma eval_lenDef (v) :
    Semiformula.Evalbm V v lenDef.val ↔ v 0 = len (v 1) := len_defined.df.iff v

instance len_definable : 𝚺₁-Function₁ (len : V → V) := Defined.to_definable _ len_defined

instance len_definable' (Γ) : (Γ, m + 1)-Function₁ (len : V → V) := .of_sigmaOne len_definable _ _

end

@[simp] lemma len_zero_iff_eq_nil {v : V} : len v = 0 ↔ v = 0 := by
  rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩) <;> simp

lemma nth_lt_len {v i : V} (hl : len v ≤ i) : v.[i] = 0 := by
  induction v using cons_induction_pi₁ generalizing i
  · definability
  case nil => simp
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hl
    simpa using ih (by simpa using hl)

end len

lemma nth_ext {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] = v₂.[i]) : v₁ = v₂ := by
  induction v₁ using cons_induction_pi₁ generalizing v₂
  · definability
  case nil =>
    exact Eq.symm <| len_zero_iff_eq_nil.mp (by simp [←hl])
  case cons x₁ v₁ ih =>
    rcases nil_or_cons v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ = x₂ := by simpa using H 0 (by simp)
    have hv : v₁ = v₂ := ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    simp [hx, hv]

lemma le_of_nth_le_nth {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] ≤ v₂.[i]) : v₁ ≤ v₂ := by
  induction v₁ using cons_induction_pi₁ generalizing v₂
  · definability
  case nil => simp
  case cons x₁ v₁ ih =>
    rcases nil_or_cons v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ ≤ x₂ := by simpa using H 0 (by simp)
    have hv : v₁ ≤ v₂ := ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    exact cons_le_cons hx hv

theorem sigmaOne_skolem_vec {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ v, len v = l ∧ ∀ i < l, R i v.[i] := by
  have : ∀ k ≤ l, ∃ v, len v = k ∧ ∀ i < k, R (l - k + i) v.[i] := by
    intro k hk
    induction k using induction_iSigmaOne
    · definability
    case zero => exact ⟨0, by simp⟩
    case succ k ih =>
      rcases ih (le_trans (by simp) hk) with ⟨v, hvk, hv⟩
      have : ∃ y, R (l - (k + 1)) y := H (l - (k + 1)) (by simp [tsub_lt_iff_left hk])
      rcases this with ⟨y, hy⟩
      exact ⟨y ∷ v, by simp [hvk], fun i hi ↦ by
        rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
        · simpa using hy
        · simpa [sub_succ_add_succ (succ_le_iff_lt.mp hk) i] using hv i (by simpa using hi)⟩
  simpa using this l (by rfl)


/-!

### Take Last k-Element

-/

namespace TakeLast

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y k | y = 0” (by simp)
  cons := .mkSigma “y x xs ih k |
    ∃ l, !lenDef l xs ∧
    (l < k → !consDef y x xs) ∧ (k ≤ l → y = ih)” (by simp)

def construction : VecRec.Construction V blueprint where
  nil _ := 0
  cons (param x xs ih) := if len xs < param 0 then x ∷ xs else ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by
    intro v
    simp [blueprint, Fin.isValue]

    show (v 0 = if len (v 2) < v 4 then v 1 ∷ v 2 else v 3) ↔
      (len (v 2) < v 4 → v 0 = v 1 ∷ v 2) ∧ (v 4 ≤ len (v 2) → v 0 = v 3)
    rcases lt_or_ge (len (v 2)) (v 4) with (hv | hv)
    · simp [hv]
    · simp [hv, not_lt_of_le hv]

end TakeLast

section takeLast

open TakeLast

def takeLast (v k : V) : V := construction.result ![k] v

@[simp] lemma takeLast_nil : takeLast (0 : V) k = 0 := by simp [takeLast, construction]

lemma takeLast_cons (x v : V) :
    takeLast (x ∷ v) k = if len v < k then x ∷ v else takeLast v k := by simp [takeLast, construction]

section

def _root_.LO.FirstOrder.Arith.takeLastDef : 𝚺₁-Semisentence 3 := blueprint.resultDef

lemma takeLast_defined : 𝚺₁-Function₂ (takeLast : V → V → V) via takeLastDef := construction.result_defined

@[simp] lemma eval_takeLastDef (v) :
    Semiformula.Evalbm V v takeLastDef.val ↔ v 0 = takeLast (v 1) (v 2) := takeLast_defined.df.iff v

instance takeLast_definable : 𝚺₁-Function₂ (takeLast : V → V → V) := Defined.to_definable _ takeLast_defined

instance takeLast_definable' (Γ) : (Γ, m + 1)-Function₂ (takeLast : V → V → V) := .of_sigmaOne takeLast_definable _ _

end

lemma len_takeLast {v k : V} (h : k ≤ len v) : len (takeLast v k) = k := by
  induction v using cons_induction_sigma₁
  · definability
  case nil => simp_all
  case cons x v ih =>
    simp [takeLast_cons]
    have : k = len v + 1 ∨ k ≤ len v := by
      rcases eq_or_lt_of_le h with (h | h)
      · left; simpa using h
      · right; simpa [lt_succ_iff_le] using h
    rcases this with (rfl | hkv)
    · simp
    · simp [not_lt_of_le hkv, ih hkv]

@[simp] lemma takeLast_len_self (v : V) : takeLast v (len v) = v := by
  rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩) <;> simp [takeLast_cons]

/-- TODO: move -/
@[simp] lemma add_sub_add (a b c : V) : (a + c) - (b + c) = a - b := add_tsub_add_eq_tsub_right a c b

@[simp] lemma takeLast_zero (v : V) : takeLast v 0 = 0 := by
  induction v using cons_induction_sigma₁
  · definability
  case nil => simp
  case cons x v ih => simp [takeLast_cons, ih]

lemma takeLast_succ_of_lt {i v : V} (h : i < len v) : takeLast v (i + 1) = v.[len v - (i + 1)] ∷ takeLast v i := by
  induction v using cons_induction_sigma₁ generalizing i
  · definability
  case nil => simp at h
  case cons x v ih =>
    simp [takeLast_cons, lt_succ_iff_le]
    rcases show i = len v ∨ i < len v from eq_or_lt_of_le (by simpa [lt_succ_iff_le] using h) with (rfl | hi)
    · simp
    · have : len v - i = len v - (i + 1) + 1 := by
        rw [←sub_sub, sub_add_self_of_le (pos_iff_one_le.mp (tsub_pos_of_lt hi))]
      simpa [not_le_of_lt hi, ↓reduceIte, this, nth_cons_succ, not_lt_of_gt hi] using ih hi

end takeLast

/-!

### Repeat

-/

section repaetVec

def repeatVec.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x | y = 0” (by simp)
  succ := .mkSigma “y ih n x | !consDef y x ih” (by simp)

def repeatVec.construction : PR.Construction V repeatVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun x _ ih ↦ x 0 ∷ ih
  zero_defined := by intro v; simp [blueprint]
  succ_defined := by intro v; simp [blueprint]; rfl

/-- `repeatVec x k = x ∷ x ∷ x ∷ ... k times ... ∷ 0`-/
def repeatVec (x k : V) : V := repeatVec.construction.result ![x] k

@[simp] lemma repeatVec_zero (x : V) : repeatVec x 0 = 0 := by simp [repeatVec, repeatVec.construction]

@[simp] lemma repeatVec_succ (x k : V) : repeatVec x (k + 1) = x ∷ repeatVec x k := by simp [repeatVec, repeatVec.construction]

section

def _root_.LO.FirstOrder.Arith.repeatVecDef : 𝚺₁-Semisentence 3 := repeatVec.blueprint.resultDef |>.rew (Rew.substs ![#0, #2, #1])

lemma repeatVec_defined : 𝚺₁-Function₂ (repeatVec : V → V → V) via repeatVecDef :=
  fun v ↦ by simp [repeatVec.construction.result_defined_iff, repeatVecDef]; rfl

@[simp] lemma eval_repeatVec (v) :
    Semiformula.Evalbm V v repeatVecDef.val ↔ v 0 = repeatVec (v 1) (v 2) := repeatVec_defined.df.iff v

instance repeatVec_definable : 𝚺₁-Function₂ (repeatVec : V → V → V) := Defined.to_definable _ repeatVec_defined

@[simp] instance repeatVec_definable' (Γ) : (Γ, m + 1)-Function₂ (repeatVec : V → V → V) :=
  .of_sigmaOne repeatVec_definable _ _

end

@[simp] lemma len_repeatVec (x k : V) : len (repeatVec x k) = k := by
  induction k using induction_iSigmaOne
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_repeatVec (x k : V) {i} (h : i < k) : (repeatVec x k).[i] = x := by
  induction k using induction_iSigmaOne generalizing i
  · definability
  case zero => simp at h
  case succ k ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using ih (by simpa using h)

lemma len_repeatVec_of_nth_le {v m : V} (H : ∀ i < len v, v.[i] ≤ m) : v ≤ repeatVec m (len v) :=
  le_of_nth_le_nth (by simp) (fun i hi ↦ by simp [nth_repeatVec m (len v) hi, H i hi])

end repaetVec

/-!

### Convert to Set

-/

namespace VecToSet

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y | y = 0” (by simp)
  cons := .mkSigma “y x xs ih | !insertDef y x ih” (by simp)

def construction : VecRec.Construction V blueprint where
  nil _ := ∅
  cons (_ x _ ih) := insert x ih
  nil_defined := by intro v; simp [blueprint, emptyset_def]
  cons_defined := by intro v; simp [blueprint]; rfl

end VecToSet

section vecToSet

open VecToSet

def vecToSet (v : V) : V := construction.result ![] v

@[simp] lemma vecToSet_nil : vecToSet (0 : V) = ∅ := by simp [vecToSet, construction]

@[simp] lemma vecToSet_cons (x v : V) :
    vecToSet (x ∷ v) = insert x (vecToSet v) := by simp [vecToSet, construction]

section

def _root_.LO.FirstOrder.Arith.vecToSetDef : 𝚺₁-Semisentence 2 := blueprint.resultDef

lemma vecToSet_defined : 𝚺₁-Function₁ (vecToSet : V → V) via vecToSetDef := construction.result_defined

@[simp] lemma eval_vecToSetDef (v) :
    Semiformula.Evalbm V v vecToSetDef.val ↔ v 0 = vecToSet (v 1) := vecToSet_defined.df.iff v

instance vecToSet_definable : 𝚺₁-Function₁ (vecToSet : V → V) := Defined.to_definable _ vecToSet_defined

instance vecToSet_definable' (Γ) : (Γ, m + 1)-Function₁ (vecToSet : V → V) := .of_sigmaOne vecToSet_definable _ _

end

lemma mem_vecToSet_iff {v x : V} : x ∈ vecToSet v ↔ ∃ i < len v, x = v.[i] := by
  induction v using cons_induction_sigma₁
  · definability
  case nil => simp
  case cons y v ih =>
    simp only [vecToSet_cons, mem_bitInsert_iff, ih, len_cons]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp [hi]⟩
    · rintro ⟨i, hi, rfl⟩
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · right; exact ⟨i, by simpa using hi, by simp⟩

@[simp] lemma nth_mem_vecToSet {v i : V} (h : i < len v) : v.[i] ∈ vecToSet v :=
  mem_vecToSet_iff.mpr ⟨i, h, rfl⟩

end vecToSet

end LO.Arith
