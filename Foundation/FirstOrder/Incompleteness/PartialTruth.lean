module

public import Foundation.FirstOrder.Bootstrapping.FixedPoint
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.R0.Basic
public import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
public import Foundation.FirstOrder.Arithmetic.Basic.Prenex

@[expose] public section
/-!
# Partial truth predicate for the arithmetical hierarchy (issue #707, Step 3)

This file defines, for each `n`, a `Σ_{n+1}` formula `sigmaTruth n` that (on `ℕ`) correctly
computes the truth value of *strict* `Σ_{n+1}` sentences (i.e. sentences literally in prenex
form, see `StrictHierarchy` in `Foundation/FirstOrder/Arithmetic/Basic/Prenex.lean`). This is a
"partial" truth predicate in the sense that no claim is made about its behaviour on formulas
that are not (codes of) strict `Σ_{n+1}` sentences.

This file is only used for the diagonalization argument in `StrictHierarchy.lean` (Step 4) and
does **not** depend on the (semantic) prenex normal form theorem
`Foundation/FirstOrder/Arithmetic/Basic/PrenexNat.lean` (Step 2).

## Implementation notes (Phase 0 skeleton)

Most lemmas below are stated with `sorry`; only the definitions `sigmaTruth`
(`sigmaTruth_zero`/`sigmaTruth_succ` in the recursive equations) are fully implemented, along with
whatever is a one-line consequence of existing simp lemmas. See the plan
`.directions/strict-arithmetic-hierarchy.md`, section "Step3/Step4 詳細プラン", §2, for the full
proof sketches.
-/

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Glue lemmas (L3-G1, L3-G2) -/

-- see plan Step3 §1.4 (G1) / §2 L3-G1.
-- `substNumeral` is (definitionally, up to the `?[t] = t ∷ 0`/`matrixToVec` unfolding) the `k = 1`
-- special case of `substNumerals`; this bridges the two so that `substNumerals_app_quote` can be
-- reused for `substNumeral`.
lemma substNumeral_eq_substNumerals (φ x : V) : substNumeral φ x = substNumerals φ ![x] := sorry

-- see plan Step3 §1.4 (G1) / §2 L3-G1. Stated over `ℕ` only, which is all Step3/Step4 need.
lemma substNumeral_app_quote_nat (π : ArithmeticSemisentence 1) (k : ℕ) :
    (substNumeral (⌜π⌝ : ℕ) (k : ℕ) : ℕ) = ⌜(π/[(↑k : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)⌝ := sorry

-- see plan Step3 §1.4 (G2) / §2 L3-G2.
-- `⌜∼σ⌝ = neg L ⌜σ⌝`: quoting commutes with negation on the nose (via `Semiformula.val_neg` and
-- the `LCWQIsoGödelQuote` instance's `neg` field).
lemma quote_neg (σ : ArithmeticSentence) : (⌜(∼σ)⌝ : V) = neg ℒₒᵣ (⌜σ⌝ : V) := sorry

/-! ### The partial truth predicate `sigmaTruth` (L3-D) -/

/-- `sigmaTruth n` is a `Σ_{n+1}` formula that, applied to (the code of) a strict `Σ_{n+1}`
sentence, correctly decides its truth value on `ℕ` (see `sigmaTruth_iff`). The base case
(`n = 0`) is the (Σ₁) provability predicate for `𝗜𝚺₁`, which by Σ₁-completeness agrees with truth
on `Σ₁` sentences. The inductive step peels off one existential quantifier: `sigmaTruth (n + 1)`
holds of `x` iff `x` is (the code of) `∃⁰ π` for some `π`, and `sigmaTruth n` fails on (the code
of) `∼(π/[k])` for some witness `k`. -/
noncomputable def sigmaTruth : ℕ → ArithmeticSemisentence 1
  | 0     => (provable 𝗜𝚺₁).val
  | n + 1 => “x. ∃ p, !qqExsDef x p ∧ ∃ k s y, !ssnum s p k ∧ !(negGraph ℒₒᵣ) y s ∧ ¬!(sigmaTruth n) y”

/-! ### Hierarchy of `sigmaTruth` (L3-1) -/

-- see plan Step3 §2 L3-1
lemma sigmaTruth_hierarchy (n : ℕ) : Hierarchy 𝚺 (n + 1) (sigmaTruth n) := sorry

/-! ### Correctness, base case (L3-2) -/

-- see plan Step3 §2 L3-2
lemma sigmaTruth_zero_iff {σ : ArithmeticSentence} (h : Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth 0)/[⌜σ⌝] ↔ ℕ↓[ℒₒᵣ] ⊧ σ := sorry

/-! ### Correctness, evaluation of the inductive step (L3-3) -/

-- see plan Step3 §2 L3-3
lemma sigmaTruth_succ_eval (n x : ℕ) :
    ℕ ⊧/![x] (sigmaTruth (n + 1)) ↔
    ∃ p : ℕ, x = qqExs p ∧ ∃ k : ℕ, ¬ℕ ⊧/![neg ℒₒᵣ (substNumeral p k)] (sigmaTruth n) := sorry

/-! ### Bridge between substitution and evaluation (L3-0) -/

-- see plan Step3 §2, auxiliary lemma right after L3-4.
lemma models_subst_iff (φ : ArithmeticSemisentence 1) (k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ φ/[(↑k : ArithmeticSemiterm Empty 0)] ↔ ℕ ⊧/![k] φ := sorry

/-! ### Correctness, main theorem (L3-4) -/

/-- Main correctness theorem for the partial truth predicate: `sigmaTruth n` agrees with actual
truth on `ℕ` for every strict `Σ_{n+1}` sentence `σ`. -/
-- see plan Step3 §2 L3-4
theorem sigmaTruth_iff : ∀ {n : ℕ} {σ : ArithmeticSentence},
    StrictHierarchy 𝚺 (n + 1) σ → (ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[⌜σ⌝] ↔ ℕ↓[ℒₒᵣ] ⊧ σ) := sorry

end LO.FirstOrder.Arithmetic
