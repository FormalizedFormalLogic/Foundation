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

-- `substNumeral` is (definitionally, up to the `?[t] = t ∷ 0`/`matrixToVec` unfolding) the `k = 1`
-- special case of `substNumerals`; this bridges the two so that `substNumerals_app_quote` can be
-- reused for `substNumeral`.
lemma substNumeral_eq_substNumerals (φ x : V) : substNumeral φ x = substNumerals φ ![x] := by
  simp [substNumeral, substNumerals, matrixToVec_succ, matrixToVec_nil]

-- Stated over `ℕ` only, which is all Step3/Step4 need.
lemma substNumeral_app_quote_nat (π : ArithmeticSemisentence 1) (k : ℕ) :
    (substNumeral (⌜π⌝ : ℕ) (k : ℕ) : ℕ) = ⌜(π/[(↑k : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)⌝ := by
  rw [substNumeral_eq_substNumerals]
  have h := substNumerals_app_quote (V := ℕ) π (![k] : Fin 1 → ℕ)
  simp only [← numeral_eq_natCast, Nat.numeral_eq] at h
  have hv : (fun i : Fin 1 ↦ (↑(((![k] : Fin 1 → ℕ)) i) : ArithmeticSemiterm Empty 0))
      = ![(↑k : ArithmeticSemiterm Empty 0)] := by
    funext i
    simp [Matrix.cons_val_fin_one]
  rwa [hv] at h;

-- `⌜∼σ⌝ = neg L ⌜σ⌝`: quoting commutes with negation on the nose (via `Semiformula.val_neg` and
-- the `LCWQIsoGödelQuote` instance's `neg` field).
lemma quote_neg (σ : ArithmeticSentence) : (⌜(∼σ)⌝ : V) = neg ℒₒᵣ (⌜σ⌝ : V) := by
  simp [Sentence.quote_eq]

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

@[simp, grind .]
lemma sigmaTruth_hierarchy (n : ℕ) : Hierarchy 𝚺 (n + 1) (sigmaTruth n) := by
  induction n with
  | zero => simp [sigmaTruth]
  | succ n ih =>
    simp only [sigmaTruth, Hierarchy.sigma_iff, Hierarchy.and_iff, Hierarchy.rew_iff, Hierarchy.neg_iff];
    refine ⟨?_, ?_, ?_, ?_⟩;
    . exact HierarchySymbol.Semiformula.hierarchy_zero _;
    . exact Hierarchy.mono (HierarchySymbol.Semiformula.hierarchy_sigma (φ := ssnum)) (by omega);
    . exact Hierarchy.mono (HierarchySymbol.Semiformula.hierarchy_sigma (φ := negGraph ℒₒᵣ)) (by omega);
    . exact ih.accum _;

/-! ### Correctness, base case (L3-2) -/

variable {σ : ArithmeticSentence}

@[simp, grind .]
lemma sigmaTruth_zero_iff (h : Hierarchy 𝚺 1 σ) : ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth 0)/[⌜σ⌝] ↔ ℕ↓[ℒₒᵣ] ⊧ σ := by
  -- `sigmaTruth 0` is (by definition) the Σ₁ provability predicate for `𝗜𝚺₁`.
  have step1 : ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth 0)/[⌜σ⌝] ↔ Provable 𝗜𝚺₁ (⌜σ⌝ : ℕ) := by
    simpa [sigmaTruth, models_iff, Matrix.constant_eq_singleton] using
      Provable.defined.defined (V := ℕ) (T := 𝗜𝚺₁) ![(⌜σ⌝ : ℕ)]
  rw [step1, Bootstrapping.provable_iff_provable]
  exact (sigma_one_completeness_iff (T := 𝗜𝚺₁) h).symm
lemma sigmaTruth_succ_eval (n x : ℕ) :
    ℕ ⊧/![x] (sigmaTruth (n + 1)) ↔
    ∃ p : ℕ, x = qqExs p ∧ ∃ k : ℕ, ¬ℕ ⊧/![neg ℒₒᵣ (substNumeral p k)] (sigmaTruth n) := by
  simp [sigmaTruth, qqExsists_defined.iff, substNumeral.defined.iff, neg.defined.iff,
    Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma models_subst_iff (φ : ArithmeticSemisentence 1) (k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ φ/[(↑k : ArithmeticSemiterm Empty 0)] ↔ ℕ ⊧/![k] φ := by
  simp [models_iff, Semiformula.eval_substs]

/-! ### Correctness, main theorem (L3-4) -/


/-- Main correctness theorem for the partial truth predicate: `sigmaTruth n` agrees with actual
truth on `ℕ` for every strict `Σ_{n+1}` sentence `σ`. -/
theorem sigmaTruth_iff : ∀ {n : ℕ} {σ : ArithmeticSentence},
    StrictHierarchy 𝚺 (n + 1) σ → (ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[⌜σ⌝] ↔ ℕ↓[ℒₒᵣ] ⊧ σ)
  | 0, σ, h => sigmaTruth_zero_iff h.hierarchy
  | n + 1, σ, h => by
      -- σ is literally `∃⁰ π` for some strict `Π_{n+1}` formula `π`.
      obtain ⟨π, rfl, hπ⟩ := h.sigma_succ_elim
      -- Bridge between `/[·]`-substitution and evaluation at the numeral `⌜∃⁰π⌝`.
      have hbridge : ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth (n + 1))/[⌜(∃⁰ π : ArithmeticSentence)⌝] ↔
          ℕ ⊧/![(⌜(∃⁰ π : ArithmeticSentence)⌝ : ℕ)] (sigmaTruth (n + 1)) := by
        simpa using models_subst_iff (sigmaTruth (n + 1)) (⌜(∃⁰ π : ArithmeticSentence)⌝ : ℕ)
      rw [hbridge, sigmaTruth_succ_eval]
      -- `⌜∃⁰π⌝ = ^∃⌜π⌝` at the level of natural number codes.
      have hq : (⌜(∃⁰ π : ArithmeticSentence)⌝ : ℕ) = qqExs (⌜π⌝ : ℕ) := by
        simp [Sentence.quote_def]
      -- `ℕ ⊧ ∃⁰π` unfolds to an actual existential over `ℕ`.
      have hex : ℕ↓[ℒₒᵣ] ⊧ (∃⁰ π : ArithmeticSentence) ↔ ∃ x : ℕ, ℕ ⊧/![x] π := by
        simp [models_iff]
      rw [hex]
      constructor
      · rintro ⟨p, hp, k, hk⟩
        rw [hq, qqExs_inj] at hp
        subst hp
        -- `τₖ := ∼(π/[↑k])` is a strict `Σ_{n+1}` sentence.
        have hτ : StrictHierarchy 𝚺 (n + 1) (∼(π/[(↑k : ArithmeticSemiterm Empty 0)])) :=
          (hπ.rew (Rew.subst ![(↑k : ArithmeticSemiterm Empty 0)])).neg
        -- glue: `neg ℒₒᵣ (substNumeral ⌜π⌝ k) = ⌜∼(π/[↑k])⌝`.
        have hglue : neg ℒₒᵣ (substNumeral (⌜π⌝ : ℕ) k) = ⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ := by
          rw [substNumeral_app_quote_nat, quote_neg]
        rw [hglue] at hk
        -- transport `hk` through the induction hypothesis for level `n`.
        have hk' : ¬ ℕ↓[ℒₒᵣ] ⊧ (∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence) := by
          have := sigmaTruth_iff hτ
          have hbridge' : ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝] ↔
              ℕ ⊧/![(⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ : ℕ)] (sigmaTruth n) := by
            simpa using models_subst_iff (sigmaTruth n) (⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ : ℕ)
          rw [hbridge'] at this
          exact fun hc => hk (this.mpr hc)
        have hk'' : ℕ↓[ℒₒᵣ] ⊧ (π/[(↑k : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
          by_contra hc
          exact hk' (by simpa using hc)
        have hπk : ℕ ⊧/![k] π := (models_subst_iff π k).mp hk''
        exact ⟨k, hπk⟩
      · rintro ⟨k, hπk⟩
        refine ⟨(⌜π⌝ : ℕ), by rw [hq], k, ?_⟩
        have hτ : StrictHierarchy 𝚺 (n + 1) (∼(π/[(↑k : ArithmeticSemiterm Empty 0)])) :=
          (hπ.rew (Rew.subst ![(↑k : ArithmeticSemiterm Empty 0)])).neg
        have hglue : neg ℒₒᵣ (substNumeral (⌜π⌝ : ℕ) k) = ⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ := by
          rw [substNumeral_app_quote_nat, quote_neg]
        rw [hglue]
        have hbridge' : ℕ↓[ℒₒᵣ] ⊧ (sigmaTruth n)/[⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝] ↔
            ℕ ⊧/![(⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ : ℕ)] (sigmaTruth n) := by
          simpa using models_subst_iff (sigmaTruth n) (⌜(∼(π/[(↑k : ArithmeticSemiterm Empty 0)]) : ArithmeticSentence)⌝ : ℕ)
        have := sigmaTruth_iff hτ
        rw [hbridge'] at this
        rw [this]
        simpa [models_iff] using (models_subst_iff π k).mpr hπk

end LO.FirstOrder.Arithmetic
