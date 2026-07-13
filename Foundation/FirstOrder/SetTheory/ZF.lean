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
lemma replacement_exists (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (h : ∀ x, ∃! y, R x y) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases hR with ⟨φ, hR⟩
  -- Put hR in a useful form
  have hR {x y : V} := by simpa using hR.iff ![x, y]
  have cond : ∀ x : V, ∃! y : V, φ.Eval ![x, y] id := by simpa [← hR] using h
  simpa [hR] using replacement_exists_eval X φ cond

lemma replacement_existsUnique (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (h : ∀ x, ∃! y, R x y) :
    ∃! Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases replacement_exists X R hR h with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all

/--
Replacement exists for a function.
-/
lemma replacement_exists_function (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let P (x y : V) : Prop := Function.Graph F y x
  have h : ∀ (x : V), ∃! y, P x y := by
    intro x
    simp only [Function.Graph, existsUnique_eq, P]
  exact replacement_exists X P (by definability) h

lemma replacement_existsUnique_function (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let P (x y : V) : Prop := Function.Graph F y x
  have h : ∀ (x : V), ∃! y, P x y := by
    intro x
    simp only [Function.Graph, existsUnique_eq, P]
  exact replacement_existsUnique X P (by definability) h

/--
The axiom of replacement.
-/
noncomputable def repl (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (h : ∀ x, ∃! y, R x y) : V := Classical.choose! (replacement_existsUnique X R hR h)

/--
The axiom of replacement, for a function.
-/
noncomputable def repl_function (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V := Classical.choose! (replacement_existsUnique_function X F hF)

end LO.FirstOrder.SetTheory
