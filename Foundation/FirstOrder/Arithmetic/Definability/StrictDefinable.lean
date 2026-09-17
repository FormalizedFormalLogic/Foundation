module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# Definability by strict-hierarchy formulas

`StrictDefinable Γ s P` says the predicate `P` on `V` is defined by a `StrictHierarchy Γ s`
formula whose free variables are read as parameters from `V`. The layering mirrors
`HierarchySymbol.Definable`, except that the polarity and the level are carried directly rather
than by a hierarchy symbol, and the strictness of the defining formula is recorded as a field
instead of by a bundled formula type.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ}

variable (Γ : Polarity) (s : ℕ)

/-- `R` is defined by the `StrictHierarchy Γ s` sentence `φ`. -/
structure IsStrictDefinedBy (R : (Fin k → V) → Prop) (φ : ArithmeticSemisentence k) : Prop where
  strictHierarchy : StrictHierarchy Γ s φ
  defined : FirstOrder.IsDefinedBy R φ

/-- `R` is defined by the `StrictHierarchy Γ s` formula `φ`, whose free variables are read as
parameters from `V`. -/
structure IsStrictDefinedByWithParam (R : (Fin k → V) → Prop) (φ : ArithmeticSemiformula V k) :
    Prop where
  strictHierarchy : StrictHierarchy Γ s φ
  defined : FirstOrder.IsDefinedByWithParam R φ

/-- `P` is defined by some `StrictHierarchy Γ s` formula with parameters from `V`. -/
class StrictDefinable {k} (P : (Fin k → V) → Prop) : Prop where
  strictDefinable : ∃ φ : ArithmeticSemiformula V k, IsStrictDefinedByWithParam Γ s P φ

abbrev StrictDefinablePred (P : V → Prop) : Prop :=
  StrictDefinable Γ s (k := 1) fun v ↦ P (v 0)

abbrev StrictDefinableRel (R : V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 2) fun v ↦ R (v 0) (v 1)

abbrev StrictDefinableRel₃ (R : V → V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 3) fun v ↦ R (v 0) (v 1) (v 2)

abbrev StrictDefinableRel₄ (R : V → V → V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 4) fun v ↦ R (v 0) (v 1) (v 2) (v 3)

variable {Γ s}

namespace StrictDefinable

/-- Strict definability transfers along a pointwise equivalence. -/
lemma of_iff {P Q : (Fin k → V) → Prop} (h : StrictDefinable Γ s Q) (H : ∀ v, P v ↔ Q v) :
    StrictDefinable Γ s P := by
  rwa [show P = Q from by funext v; simp [H]];

/-- A strictly definable predicate is definable. -/
lemma definable {P : (Fin k → V) → Prop} (h : StrictDefinable Γ s P) : Γ-[s].Definable P := by
  obtain ⟨φ, hs, hφ⟩ := h;
  exact .mkPolarity φ hs.hierarchy fun v ↦ (hφ v).symm;

/-- The defining formula can be taken with `ℕ`-indexed free variables. -/
lemma exists_eval_iff {P : (Fin k → V) → Prop} (h : StrictDefinable Γ s P) :
    ∃ (e : ℕ → V) (φ : ArithmeticSemiformula ℕ k),
      StrictHierarchy Γ s φ ∧ ∀ v, P v ↔ φ.Eval v e := by
  classical
  obtain ⟨φ, hs, hφ⟩ := h;
  have : Inhabited V := Classical.inhabited_of_nonempty';
  use φ.enumerateFVar, Rew.rewriteMap φ.idxOfFVar ▹ φ;
  and_intros;
  . exact hs.rew _;
  . intro v;
    simp [Semiformula.eval_rewriteMap, hφ];

/-- A `StrictHierarchy Γ s` sentence, read against an environment for its trailing bound variables,
strictly defines the binary relation given by its two leading bound variables. -/
lemma of_strictHierarchy {m : ℕ} {θ : ArithmeticSemisentence (m + 2)}
    (hθ : StrictHierarchy Γ s θ) (e : Fin m → V) :
    StrictDefinableRel Γ s fun x y ↦ V ⊧/(y :> x :> e) θ := by
  constructor;
  use Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2)) ▹ θ;
  constructor;
  . exact hθ.rew _;
  . intro v;
    simp only [Semiformula.eval_embSubsts];
    apply Iff.of_eq;
    apply congrArg fun w ↦ Semiformula.Evalb (M := V) w θ;
    funext i;
    cases i using Fin.cases with
    | zero => simp;
    | succ i =>
      cases i using Fin.cases with
      | zero => simp;
      | succ i => simp;

end StrictDefinable

end FFL.FirstOrder.Arithmetic
