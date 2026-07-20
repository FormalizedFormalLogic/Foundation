module

public import Foundation.FirstOrder.SetTheory.Z

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ## Ersatzaxiom -/

open Classical

lemma replacement_exists_eval (φ : SetTheorySemiformula V 2) (X : V) (h : (∀ x : V, ∃! y : V, φ.Eval ![x, y] id)) :
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
lemma replacement_rel_exists (R : V → V → Prop) (X : V) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases hR with ⟨φ, hR⟩
  -- Put hR in a useful form
  have hR {x y : V} := by simpa using hR.iff ![x, y]
  have cond : ∀ x : V, ∃! y : V, φ.Eval ![x, y] id := by simpa [← hR] using h
  simpa [hR] using replacement_exists_eval φ X cond

/--
Replacement exists uniquely (for a relation).
-/
lemma replacement_rel_existsUnique (R : V → V → Prop) (X : V) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃! Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases replacement_rel_exists R X h hR with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all

/--
Replacement exists uniquely for a function.
-/
lemma replacement_existsUnique (F : V → V) (X : V) (hF : ℒₛₑₜ-function₁ F) :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let R (x y : V) : Prop := Function.Graph F y x
  have h : ∀ (x : V), ∃! y, R x y := by
    intro x
    simp only [Function.Graph, existsUnique_eq, R]
  exact replacement_rel_existsUnique R X h (by definability)

/--
Replacement exists for a function.
-/
lemma replacement_exists (F : V → V) (X : V) (hF : ℒₛₑₜ-function₁ F) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := (replacement_existsUnique F X hF).exists

/--
The axiom of replacement for a relation.
-/
noncomputable def replRel (R : V → V → Prop) (X : V) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R := by definability) : V := Classical.choose! (replacement_rel_existsUnique R X h hR)

/--
The axiom of replacement.
-/
noncomputable def repl (F : V → V) (X : V) (hF : ℒₛₑₜ-function₁ F := by definability) : V := Classical.choose! (replacement_existsUnique F X hF)

/-! ## Variants of replacement -/

/--
A stronger variant of (unique existence of) replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_existsUnique_of_mem_existsUnique (R : V → V → Prop) (X : V) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
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
  obtain ⟨Y, hY⟩ := replacement_rel_exists R' X cond (by definability)
  use Y
  aesop

/--
A stronger variant of replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_exists_of_mem_existsUnique (R : V → V → Prop) (X : V) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := (replacement_rel_existsUnique_of_mem_existsUnique R X h hR).exists

/--
The axiom of replacement, only assuming uniqueness on `X`.
-/
noncomputable def replRelOverSet (R : V → V → Prop) (X : V) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R := by definability) : V :=
  Classical.choose! (replacement_rel_existsUnique_of_mem_existsUnique R X h hR)

/-! ## Various lemmas -/

@[simp] lemma replRel_spec {R : V → V → Prop} {X y : V} {h : ∀ x, ∃! y, R x y} (hR : ℒₛₑₜ-relation R) :
    y ∈ replRel R X h ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique R X h hR) y

@[simp] lemma repl_spec {F : V → V} {X y : V} (hF : ℒₛₑₜ-function₁ F) :
    y ∈ repl F X hF ↔ ∃ x ∈ X, y = F x := Classical.choose!_spec (replacement_existsUnique F X hF) y

@[simp] lemma replRelOverSet_spec {R : V → V → Prop} {X y : V} {h : ∀ x ∈ X, ∃! y, R x y} (hR : ℒₛₑₜ-relation R) :
    y ∈ replRelOverSet R X h ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique_of_mem_existsUnique R X h hR) y


/-! ### Definability Gadgets for Replacement -/

namespace Repl

structure Blueprint (arity : ℕ) where
  graph : SetTheorySemisentence (arity + 2)

def Blueprint.resultDef (b : Blueprint arity) : SetTheorySemisentence (arity + 2) :=
  “Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !b.graph y x ⋯”

variable (V)

structure Construction {arity : ℕ} (b : Blueprint arity) where
  map : (Fin arity → V) → V → V
  map_defined : DefinedFunction (fun v ↦ map (v ·.succ) (v 0)) b.graph

variable {V}

namespace Construction

variable {arity : ℕ} {b : Blueprint arity} (c : Construction V b)

instance map_definable :
  (ℒₛₑₜ).DefinableFunction (fun v ↦ c.map (v ·.succ) (v 0)) := c.map_defined.to_definable

noncomputable def result (v : Fin arity → V) : V → V := fun x ↦ repl x (c.map v) (by
  refine ⟨(Rew.embSubsts (#0 :> #1 :> fun i : Fin arity ↦ &(v i))) ▹ b.graph, ?_⟩
  intro x
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.map_defined.iff (x 0 :> x 1 :> v))

lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) b.resultDef := .mk fun v ↦ by
  constructor
  · intro h
    simp [Blueprint.resultDef] at h
    ext y
    simpa [result, c.map_defined.iff] using h y
  · intro h
    simp [Blueprint.resultDef, result, c.map_defined.iff, h]

@[simp] lemma eval_resultDef : b.resultDef.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v

@[simp] lemma mem_result : y ∈ c.result v X ↔ ∃ x ∈ X, y = c.map v x := by
  simp [result, repl_spec]

end Construction

end Repl

end LO.FirstOrder.SetTheory
