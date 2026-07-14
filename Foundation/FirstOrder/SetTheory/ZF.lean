module

public import Foundation.FirstOrder.SetTheory.Z

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ## Ersatzaxiom -/

open Classical

lemma replacement_exists_eval (X : V) (φ : SetTheorySemiformula V 2) (h : (∀ x : V, ∃! y : V, φ.Eval ![x, y] id)) :
    ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, φ.Eval ![x, y] id := by
  /- `φ` can have finitely many free variables of type `V`, these are interpreted by `id : V → V` as finitely many parameters in `V`.
  `f` enumerates the parameters of `φ`. -/
  let f := φ.enumarateFVar
  /- While `φ` has free variables of type `V`, `ψ` has free variables of type `ℕ`.
  Since `f` enumerates the parameters, it is intended to be the valuation of the free variables of `ψ`. -/
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ

  have whole := by simpa [models_iff, Semiformula.eval_univCl, Axiom.replacementSchema] using Theory.models V 𝗭𝗙 (ZermeloFraenkel.axiom_of_replacement ψ)

  have cond : ∀ x, ∃! y : V, ψ.Eval ![x, y] f := by
    simpa [ψ, f, Semiformula.eval_rewriteMap]

  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton] using whole f cond X

/--
Replacement exists (for a relation).
-/
lemma replacement_rel_exists (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x, ∃! y, R x y) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases hR with ⟨φ, hR⟩
  -- Put hR in a useful form
  have hR {x y : V} := by simpa using hR.iff ![x, y]
  have cond : ∀ x : V, ∃! y : V, φ.Eval ![x, y] id := by simpa [← hR] using h
  simpa [hR] using replacement_exists_eval X φ cond

/--
Replacement exists uniquely (for a relation).
-/
lemma replacement_rel_existsUnique (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x, ∃! y, R x y) :
    ∃! Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases replacement_rel_exists X R h with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all

/--
Replacement exists uniquely for a function.
-/
lemma replacement_existsUnique (X : V) (F : V → V) [hF : ℒₛₑₜ-function₁ F] :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let R (x y : V) : Prop := Function.Graph F y x
  have h : ∀ (x : V), ∃! y, R x y := by
    intro x
    simp only [Function.Graph, existsUnique_eq, R]
  exact replacement_rel_existsUnique X R (hR := by definability) h

/--
Replacement exists for a function.
-/
lemma replacement_exists (X : V) (F : V → V) [hF : ℒₛₑₜ-function₁ F] :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := (replacement_existsUnique X F).exists

/--
The axiom of replacement for a relation.
-/
noncomputable def replRel (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x, ∃! y, R x y) : V := Classical.choose! (replacement_rel_existsUnique X R h)

/--
The axiom of replacement.
-/
noncomputable def repl (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V := Classical.choose! (replacement_existsUnique X F)

/-! ## Various lemmas -/

@[simp] lemma replRel_spec {X y : V} {R : V → V → Prop} [hR : ℒₛₑₜ-relation R] {h : ∀ x, ∃! y, R x y} :
    y ∈ replRel X R h ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique X R h) y

/-! ## Variants of replacement -/

/--
A stronger variant of (unique existent of) replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_existsUnique_of_mem_existsUnique (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x ∈ X, ∃! y, R x y) :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  /- Proof sketch: Define `R' x y` to hold iff `x ∈ X` and `R x y`, or `x ∉ X` and `y = ∅`.
  Show that `∀ x, ∃! y, R' x y` holds, by case subdivision on whether `x ∈ X` or not.
  Obtain `Y` from replacement.
  Then, for any `y`, we have that `y ∈ Y` iff `∃ x ∈ X, R x y`, iff `∃ x ∈ X, R' x y`.
  -/
  let R' (x y : V) : Prop := x ∈ X ∧ R x y ∨ x ∉ X ∧ y = ∅
  have cond : ∀ x, ∃! y, R' x y := by
    intro x
    refine Classical.byCases (p := x ∈ X) ?_ ?_ <;> (intro hx; simp_all [R'])
  obtain ⟨Y, hY⟩ := replacement_rel_exists X R' (hR := by definability) cond
  use Y
  aesop

/--
A stronger variant of replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_exists_of_mem_existsUnique (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x ∈ X, ∃! y, R x y) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := (replacement_rel_existsUnique_of_mem_existsUnique X R h).exists

/--
The axiom of replacement, only assuming uniqueness on `X`.
-/
noncomputable def replRelOfMemExistsUnique (X : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] (h : ∀ x ∈ X, ∃! y, R x y) : V :=
  Classical.choose! (replacement_rel_existsUnique_of_mem_existsUnique X R h)

/--
`repl_of_mem_existsUnique` agrees with `repl`.
TODO: This is not very useful, since it already assumes uniqueness on all of `V`.
-/
@[simp] lemma replRelOfMemExistsUnique_spec {X y : V} {R : V → V → Prop} [hR : ℒₛₑₜ-relation R] {h : ∀ x ∈ X, ∃! y, R x y} :
    y ∈ replRelOfMemExistsUnique X R h ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique_of_mem_existsUnique X R h) y

end LO.FirstOrder.SetTheory
