import Arithmetization.ISigmaOne.HFS.Fixpoint

/-!

# Vec

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

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

lemma nth_graph (v i : V) : Graph ⟪v, i, nth v i⟫ :=
  Classical.choose!_spec (graph_existsUnique v i)

lemma nth_eq_of_graph {v i x : V} (h : Graph ⟪v, i, x⟫) : nth v i = x := graph_unique (nth_graph v i) h

lemma nth_zero (v : V) : nth v 0 = fstIdx v := nth_eq_of_graph (graph_zero.mpr rfl)

lemma nth_succ (v i : V) : nth v (i + 1) = nth (sndIdx v) i := nth_eq_of_graph (graph_succ.mpr <| nth_graph _ _)

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

lemma nil_or_cons (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v := by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨π₁ z, π₂ z, by simp [succ_eq_cons]⟩

@[simp] lemma cons_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [cons_def]

@[simp] lemma nth_cons_zero (x v : V) : nth (x ∷ v) 0 = x := by
  simp [nth_zero]

@[simp] lemma nth_cons_succ (x v i : V) : nth (x ∷ v) (i + 1) = nth v i := by
  simp [nth_succ]

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

end

/-- TODO: move-/
lemma pi₁_zero : π₁ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₁_le_self 0)

lemma pi₂_zero : π₂ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₂_le_self 0)

@[simp] lemma nth_zero_idx (i : V) : nth 0 i = 0 := by
  induction i using induction_iSigmaOne
  · definability
  case zero => simp [nth_zero, fstIdx, pi₁_zero]
  case succ i ih => simp [nth_succ, sndIdx, pi₂_zero, ih]

lemma nth_lt_of_pos {v} (hv : 0 < v) (i : V) : nth v i < v := by
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

@[simp] lemma nth_le (v i : V) : nth v i ≤ v := by
  rcases eq_zero_or_pos v with (h | h)
  · simp [h]
  · exact le_of_lt <| nth_lt_of_pos h i

end nth

namespace Len

def Phi (C : Set V) (pr : V) : Prop :=
  pr = ⟪0, 0⟫ ∨ (∃ v i, v ≠ 0 ∧ pr = ⟪v, i + 1⟫ ∧ ⟪sndIdx v, i⟫ ∈ C)

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    pr = ⟪0, 0⟫ ∨
    (∃ v ≤ pr, ∃ i ≤ pr, v ≠ 0 ∧ pr = ⟪v, i + 1⟫ ∧ ∃ snd ≤ v, snd = sndIdx v ∧ ∃ six < C, six = ⟪snd, i⟫ ∧ six ∈ C) := by
  constructor
  · rintro (rfl | ⟨v, i, hv, rfl, hC⟩)
    · left; rfl
    · right; exact ⟨v, by simp,
        i, le_trans le_self_add (le_pair_right _ _),
        hv, rfl, _, by simp, rfl, _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨v, _, _, _, rfl, rfl⟩ | ⟨v, _, i, _, hv, rfl, _, _, rfl, _, _, rfl, hC⟩)
    · left; rfl
    · right; exact ⟨v, i, hv, rfl, hC⟩

def blueprint : Fixpoint.Blueprint 0 where
  core := .ofZero
    (.mkSigma “pr C |
      !pairDef pr 0 0 ∨
      (∃ v <⁺ pr, ∃ i <⁺ pr, v ≠ 0 ∧ !pairDef pr v (i + 1) ∧
        ∃ snd <⁺ v, !sndIdxDef snd v ∧ ∃ six < C, !pairDef six snd i ∧ six ∈ C)”
    (by simp))
    _

def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| by intro v; simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, hv, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, hv, rfl, hC h⟩

instance : construction.Finite V where
  finite := by
    rintro C v x (h | ⟨v, i, hv, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪sndIdx v, i⟫ + 1, Or.inr ⟨v, i, hv, rfl, h, by simp⟩⟩

def Graph : V → Prop := construction.Fixpoint ![]

section

def graphDef : 𝚺₁-Semisentence 1 := blueprint.fixpointDef

lemma graph_defined : 𝚺₁-Predicate (Graph : V → Prop) via graphDef :=
  construction.fixpoint_defined

instance graph_definable : 𝚺₁-Predicate (Graph : V → Prop) := Defined.to_definable _ graph_defined

end

lemma graph_case {pr : V} :
    Graph pr ↔ pr = ⟪0, 0⟫ ∨ (∃ v i, v ≠ 0 ∧ pr = ⟪v, i + 1⟫ ∧ Graph ⟪sndIdx v, i⟫) :=
  construction.case

lemma graph_zero {l : V} :
    Graph ⟪0, l⟫ ↔ l = 0 := by
  constructor
  · intro h
    rcases graph_case.mp h with (h | ⟨v, i, hv, h, _⟩)
    · simp at h; rcases h with ⟨rfl, rfl⟩; rfl
    · simp at h; rcases h with ⟨rfl, rfl⟩; simp at hv
  · rintro rfl; exact graph_case.mpr <| Or.inl rfl

lemma graph_succ {v x : V} :
    Graph ⟪x ∷ v, l⟫ ↔ ∃ l', l = l' + 1 ∧ Graph ⟪v, l'⟫ := by
  constructor
  · intro h
    rcases graph_case.mp h with (h | ⟨v, l, hv, h, hg⟩)
    · simp at h
    · simp at h; rcases h with ⟨rfl, rfl⟩; exact ⟨l, rfl, by simpa using hg⟩
  · rintro ⟨l, rfl, h⟩; exact graph_case.mpr <| Or.inr ⟨x ∷ v, l, by simp, rfl, by simpa using h⟩

lemma graph_exists (v : V) : ∃ l, Graph ⟪v, l⟫ := by
  induction v using cons_induction_sigma₁
  · definability
  case nil =>
    exact ⟨0, graph_zero.mpr rfl⟩
  case cons x v ih =>
    · rcases ih with ⟨l, hl⟩
      exact ⟨l + 1, graph_succ.mpr ⟨l, rfl, hl⟩⟩

lemma graph_unique {v l₁ l₂ : V} : Graph ⟪v, l₁⟫ → Graph ⟪v, l₂⟫ → l₁ = l₂ := by
  induction v using cons_induction_pi₁ generalizing l₁ l₂
  · definability
  case nil =>
    simp [graph_zero]; rintro rfl rfl; rfl
  case cons x v ih =>
    simp [graph_succ]
    rintro l₁ rfl h₁ l₂ rfl h₂
    rcases ih h₁ h₂; rfl

lemma graph_existsUnique (v : V) : ∃! l, Graph ⟪v, l⟫ := by
  rcases graph_exists v with ⟨l, hl⟩
  exact ExistsUnique.intro l hl (fun y hy ↦ graph_unique hy hl)

end Len

section len

open Len

def len (v : V) : V := Classical.choose! (graph_existsUnique v)

lemma len_graph (v : V) : Graph ⟪v, len v⟫ := Classical.choose!_spec (graph_existsUnique v)

lemma len_eq_of_graph {v l : V} (h : Graph ⟪v, l⟫) : len v = l := graph_unique (len_graph v) h

@[simp] lemma len_nil : len (0 : V) = 0 := len_eq_of_graph (graph_zero.mpr rfl)

@[simp] lemma len_cons (x v : V) : len (x ∷ v) = len v + 1 := len_eq_of_graph (graph_succ.mpr ⟨_, rfl, len_graph v⟩)

section

def _root_.LO.FirstOrder.Arith.lenDef : 𝚺₁-Semisentence 2 :=
  .mkSigma “l v | ∃ pr, !pairDef pr v l ∧ !graphDef pr” (by simp)

lemma len_defined : 𝚺₁-Function₁ (len : V → V) via lenDef := by
  intro v; simp [lenDef, graph_defined.df.iff]
  constructor
  · intro h; rw [h]; exact len_graph _
  · intro h; rw [len_eq_of_graph h]

@[simp] lemma eval_lenDef (v) :
    Semiformula.Evalbm V v lenDef.val ↔ v 0 = len (v 1) := len_defined.df.iff v

instance len_definable : 𝚺₁-Function₁ (len : V → V) := Defined.to_definable _ len_defined

instance len_definable' (Γ) : (Γ, m + 1)-Function₁ (len : V → V) := .of_sigmaOne len_definable _ _

end

@[simp] lemma len_zero_iff_eq_nil {v : V} : len v = 0 ↔ v = 0 := by
  rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩) <;> simp

lemma nth_lt_len {v i : V} (hl : len v ≤ i) : nth v i = 0 := by
  induction v using cons_induction_pi₁ generalizing i
  · definability
  case nil => simp
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hl
    simpa using ih (by simpa using hl)

lemma nth_ext {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, nth v₁ i = nth v₂ i) : v₁ = v₂ := by
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

end len

end LO.Arith
