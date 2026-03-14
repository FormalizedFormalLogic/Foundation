module

public import Foundation.FirstOrder.SetTheory.Z

@[expose] public section

namespace LO.FirstOrder.SetTheory

lemma functionGraph_functionLike {V : Type*} (F : V → V) :
    ∀ x : V, ∃! y : V, Function.Graph F y x := by
  intro x
  refine ⟨F x, rfl, ?_⟩
  intro y hy
  simpa [Function.Graph] using hy

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭𝗙]

/-! ## Ersatzaxiom -/

open Classical

lemma replacement_exists_eval (φ : Semiformula ℒₛₑₜ V 2) :
    (∀ x : V, ∃! y : V, Semiformula.Evalm V ![x, y] id φ) →
      ∀ X : V, ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, Semiformula.Evalm V ![x, y] id φ := by
  have : Inhabited V := inhabited_of_nonempty inferInstance
  let f := φ.enumarateFVar
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  have := by
    simpa [models_iff, Semiformula.eval_univCl, Axiom.replacementSchema] using
      ModelsTheory.models V (ZermeloFraenkel.axiom_of_replacement ψ)
  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton, Matrix.comp_vecCons'] using this f

lemma replacement_exists (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R) :
    (∀ x : V, ∃! y : V, R x y) →
      ∀ X : V, ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases hR with ⟨φ, hφ⟩
  simpa [hφ.iff] using replacement_exists_eval (V := V) φ

variable [V ⊧ₘ* 𝗭]

noncomputable scoped instance : EmptyCollection V := ⟨Classical.choose! LO.FirstOrder.SetTheory.empty_existsUnique⟩

/--
Restricted replacement: from uniqueness only on `X`, collect exactly the images of elements of `X`.
-/
lemma replacement_exists_on (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R)
    (hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y) :
    ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  let Rt : V → V → Prop := fun x y ↦ (x ∈ X ∧ R x y) ∨ (x ∉ X ∧ y = ∅)
  have hRt : ℒₛₑₜ-relation[V] Rt := by
    classical
    change ℒₛₑₜ-relation[V] (fun x y ↦ (x ∈ X ∧ R x y) ∨ (x ∉ X ∧ y = ∅))
    definability
  have hfunRt : ∀ x : V, ∃! y : V, Rt x y := by
    intro x
    by_cases hx : x ∈ X
    · rcases hfun x hx with ⟨y, hy, hyu⟩
      refine ⟨y, ?_, ?_⟩
      · exact Or.inl ⟨hx, hy⟩
      · intro y' hy'
        rcases hy' with (⟨_, hy'⟩ | ⟨hx', _⟩)
        · exact hyu _ hy'
        · exact absurd hx hx'
    · refine ⟨∅, ?_, ?_⟩
      · exact Or.inr ⟨hx, rfl⟩
      · intro y hy
        rcases hy with (⟨hx', _⟩ | ⟨_, hy⟩)
        · exact absurd hx' hx
        · exact hy
  rcases replacement_exists Rt hRt hfunRt X with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro y
  constructor
  · intro hy
    rcases (hY y).1 hy with ⟨x, hxX, hxy⟩
    rcases hxy with (⟨_, hRxy⟩ | ⟨hxnX, _⟩)
    · exact ⟨x, hxX, hRxy⟩
    · exact (hxnX hxX).elim
  · rintro ⟨x, hxX, hRxy⟩
    exact (hY y).2 ⟨x, hxX, Or.inl ⟨hxX, hRxy⟩⟩

/--
Restricted replacement for definable unary functions:
collect exactly the values `F x` for `x ∈ X`.
-/
lemma replacement_exists_on_of_definableFunction (X : V) (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let R : V → V → Prop := fun x y ↦ Function.Graph F y x
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    change ℒₛₑₜ-relation[V] (fun x y ↦ Function.Graph F y x)
    definability
  have hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y := by
    intro x _
    simpa [R] using functionGraph_functionLike F x
  rcases replacement_exists_on (X := X) R hR hfun with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro y
  simpa [R, Function.Graph] using hY y

lemma replacement_existsUnique (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R)
    (hfun : ∀ x : V, ∃! y : V, R x y) :
    ∃! Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases replacement_exists R hR hfun X with ⟨Y, hY⟩
  refine ⟨Y, hY, ?_⟩
  intro Y' hY'
  ext y
  simp [hY y, hY' y]

noncomputable def repl (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R)
    (hfun : ∀ x : V, ∃! y : V, R x y) : V :=
  Classical.choose! (replacement_existsUnique X R hR hfun)

@[simp] lemma mem_repl_iff {X y : V} {R : V → V → Prop} {hR : ℒₛₑₜ-relation[V] R}
    {hfun : ∀ x : V, ∃! y : V, R x y} :
    y ∈ repl X R hR hfun ↔ ∃ x ∈ X, R x y :=
  Classical.choose!_spec (replacement_existsUnique X R hR hfun) y
