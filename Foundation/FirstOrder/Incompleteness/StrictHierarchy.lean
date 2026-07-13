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
    Hierarchy 𝚺 (n + 1) (diagNeg ψ) := by
  simp only [diagNeg]
  refine Hierarchy.sigma_iff.mpr (Hierarchy.and_iff.mpr ⟨?_, Hierarchy.neg_iff.mpr (by simpa using h)⟩)
  simpa using Hierarchy.mono (Γ := 𝚺) (s := 1) (by simp) (show (1 : ℕ) ≤ n + 1 by omega)

-- see plan Step4 §3 L4-2
lemma diagNeg_eval (ψ : ArithmeticSemisentence 1) (x : ℕ) :
    ℕ ⊧/![x] (diagNeg ψ) ↔ ¬ℕ ⊧/![substNumeral x x] ψ := by
  simp [diagNeg]

/-! ### Diagonalization (L4-3) -/

-- see plan Step4 §3 L4-3
set_option maxHeartbeats 800000 in
/-- No `Π_{n+1}` formula agrees everywhere with the partial truth predicate `sigmaTruth n`. -/
theorem sigmaTruth_not_pi (n : ℕ) :
    ¬∃ ψ : ArithmeticSemisentence 1, Hierarchy 𝚷 (n + 1) ψ ∧
      ∀ k : ℕ, ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[(↑k : ArithmeticSemiterm Empty 0)] ↔
        ℕ↓[ℒₒᵣ] ⊧ ψ/[(↑k : ArithmeticSemiterm Empty 0)] := by
  rintro ⟨ψ, hψ, hagree⟩
  have hδ₀ : Hierarchy 𝚺 (n + 1) (diagNeg ψ) := diagNeg_hierarchy hψ
  -- Step2 dependency: only the *signature* of `hierarchy_equivStrict` is used here.
  obtain ⟨δ', hδ's, hδ'iff⟩ := EquivStrict.hierarchy_equivStrict hδ₀ (by omega)
  -- `σ₀` is the self-referential sentence obtained by substituting the code of `δ'` into itself.
  set σ₀ : ArithmeticSentence := δ'/[(⌜δ'⌝ : ArithmeticSemiterm Empty 0)] with hσ₀_def
  have hσ₀s : StrictHierarchy 𝚺 (n + 1) σ₀ :=
    hδ's.rew (Rew.subst ![(⌜δ'⌝ : ArithmeticSemiterm Empty 0)])
  -- G1-style key identity: self-applying `substNumeral` to (the code of) `δ'` yields (the code
  -- of) `σ₀`. Same pattern as the `fixedpoint` construction in `FixedPoint.lean`.
  have hkey : substNumeral (⌜δ'⌝ : ℕ) (⌜δ'⌝ : ℕ) = (⌜σ₀⌝ : ℕ) := substNumeral_app_quote δ' δ'
  -- Evaluation chain: `ℕ ⊧ σ₀ ↔ ¬ℕ ⊧ σ₀`, a contradiction.
  have step1 : ℕ↓[ℒₒᵣ] ⊧ σ₀ ↔ ℕ ⊧/![(⌜δ'⌝ : ℕ)] δ' := by
    have h := models_subst_iff δ' (⌜δ'⌝ : ℕ)
    rwa [Sentence.coe_quote] at h
  have step2 : ℕ ⊧/![(⌜δ'⌝ : ℕ)] δ' ↔ ℕ ⊧/![(⌜δ'⌝ : ℕ)] (diagNeg ψ) := hδ'iff ![(⌜δ'⌝ : ℕ)]
  have step3 : ℕ ⊧/![(⌜δ'⌝ : ℕ)] (diagNeg ψ) ↔ ¬ℕ ⊧/![(⌜σ₀⌝ : ℕ)] ψ := by
    have h := diagNeg_eval ψ (⌜δ'⌝ : ℕ)
    rwa [hkey] at h
  have step4 : ¬ℕ ⊧/![(⌜σ₀⌝ : ℕ)] ψ ↔
      ¬ℕ↓[ℒₒᵣ] ⊧ ψ/[(↑(⌜σ₀⌝ : ℕ) : ArithmeticSemiterm Empty 0)] :=
    not_congr (models_subst_iff ψ (⌜σ₀⌝ : ℕ)).symm
  have step5 : ¬ℕ↓[ℒₒᵣ] ⊧ ψ/[(↑(⌜σ₀⌝ : ℕ) : ArithmeticSemiterm Empty 0)] ↔
      ¬ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[(↑(⌜σ₀⌝ : ℕ) : ArithmeticSemiterm Empty 0)] :=
    not_congr (hagree (⌜σ₀⌝ : ℕ)).symm
  have step6 : ¬ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[(↑(⌜σ₀⌝ : ℕ) : ArithmeticSemiterm Empty 0)] ↔
      ¬ℕ↓[ℒₒᵣ] ⊧ σ₀ := by
    rw [Sentence.coe_quote]
    exact not_congr (sigmaTruth_iff hσ₀s)
  have hcontra : ℕ↓[ℒₒᵣ] ⊧ σ₀ ↔ ¬ℕ↓[ℒₒᵣ] ⊧ σ₀ :=
    step1.trans <| step2.trans <| step3.trans <| step4.trans <| step5.trans step6
  tauto

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
