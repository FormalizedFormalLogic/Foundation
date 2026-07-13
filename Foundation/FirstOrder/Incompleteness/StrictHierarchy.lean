module

public import Foundation.FirstOrder.Incompleteness.PartialTruth
public import Foundation.FirstOrder.Arithmetic.Basic.PrenexNat

@[expose] public section
/-!
# Strictness of the arithmetical hierarchy (issue #707, Step 4)

Main theorem: for every `n`, there is a `Σ_{n+1}` predicate (namely `sigmaTruth n` from
`PartialTruth.lean`) that is not `Π_{n+1}`-definable on `ℕ`. This is proved by a direct
diagonalization (no fixed-point machinery needed): assuming a `Π_{n+1}` formula `ψ` agrees with
`sigmaTruth n` everywhere, `diagNeg ψ` is a `Σ_{n+1}` formula whose (semantic) prenex normal form
`δ'` (via `EquivStrict.hierarchy_equivStrict` from Step 2, `PrenexNat.lean`) yields a
self-referential sentence `σ₀ := δ'/[⌜δ'⌝]` with `ℕ ⊧ σ₀ ↔ ¬ℕ ⊧ σ₀`, a contradiction.

## Implementation notes (Phase 0 skeleton)

Only `diagNeg` is fully implemented; the remaining lemmas are stated with `sorry`. See the plan
`.directions/strict-arithmetic-hierarchy.md`, section "Step3/Step4 詳細プラン", §3, for the full
proof sketches. The only point where this file depends on Step 2
(`EquivStrict.hierarchy_equivStrict`) is inside the proof of `sigmaTruth_not_pi`; the *signature*
of `hierarchy_equivStrict` is stable already, so this file type-checks (up to the stated `sorry`s)
regardless of whether Step 2 itself is finished.
-/

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

/-! ### The diagonal formula (L4-1, L4-2) -/

/-- Given a formula `ψ`, `diagNeg ψ` is the formula `x ↦ ¬ψ(substNumeral x x)`, i.e. the
"self-application negation" of `ψ`. This is the same pattern as `Bootstrapping.diag`
(`FixedPoint.lean`), but without the fixed-point wrapper: we only need the formula itself, and
later push it through the (semantic) prenex normal form theorem instead of the provability-based
fixed point lemma. -/
noncomputable def diagNeg (ψ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
  “x. ∃ y, !ssnum y x x ∧ ¬!ψ y”

-- see plan Step4 §3 L4-1
lemma diagNeg_hierarchy {n : ℕ} {ψ : ArithmeticSemisentence 1} (h : Hierarchy 𝚷 (n + 1) ψ) :
    Hierarchy 𝚺 (n + 1) (diagNeg ψ) := sorry

-- see plan Step4 §3 L4-2
lemma diagNeg_eval (ψ : ArithmeticSemisentence 1) (x : ℕ) :
    ℕ ⊧/![x] (diagNeg ψ) ↔ ¬ℕ ⊧/![substNumeral x x] ψ := sorry

/-! ### Diagonalization (L4-3) -/

/-- No `Π_{n+1}` formula agrees everywhere with the partial truth predicate `sigmaTruth n`. -/
-- see plan Step4 §3 L4-3
theorem sigmaTruth_not_pi (n : ℕ) :
    ¬∃ ψ : ArithmeticSemisentence 1, Hierarchy 𝚷 (n + 1) ψ ∧
      ∀ k : ℕ, ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[(↑k : ArithmeticSemiterm Empty 0)] ↔
        ℕ↓[ℒₒᵣ] ⊧ ψ/[(↑k : ArithmeticSemiterm Empty 0)] := by
  rintro ⟨ψ, hψ, hagree⟩
  have hδ₀ : Hierarchy 𝚺 (n + 1) (diagNeg ψ) := diagNeg_hierarchy hψ
  -- Step2 dependency: only the *signature* of `hierarchy_equivStrict` is used here.
  obtain ⟨δ', hδ's, hδ'iff⟩ := EquivStrict.hierarchy_equivStrict hδ₀ (by omega)
  sorry

/-! ### Main theorem (L4-4) -/

/-- The arithmetical hierarchy is strict: for every `n`, there is a `Σ_{n+1}` predicate that is
not equivalent (on `ℕ`) to any `Π_{n+1}` predicate. -/
-- see plan Step4 §3 L4-4
theorem strict_arithmetical_hierarchy (n : ℕ) :
    ∃ φ : ArithmeticSemisentence 1, Hierarchy 𝚺 (n + 1) φ ∧
      ∀ ψ : ArithmeticSemisentence 1, Hierarchy 𝚷 (n + 1) ψ →
        ¬∀ k : ℕ, ℕ↓[ℒₒᵣ] ⊧ φ/[(↑k : ArithmeticSemiterm Empty 0)] ↔
          ℕ↓[ℒₒᵣ] ⊧ ψ/[(↑k : ArithmeticSemiterm Empty 0)] :=
  ⟨sigmaTruth n, sigmaTruth_hierarchy n, fun ψ hψ h => sigmaTruth_not_pi n ⟨ψ, hψ, h⟩⟩

end LO.FirstOrder.Arithmetic
