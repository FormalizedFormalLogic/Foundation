import Book.Init

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.unusedSectionVars false

open LO Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Internal InternalArithmetic

set_option verso.docstring.allowMissing true

#doc (Manual) "Gödel's First Incompleteness Theorem" =>
%%%
tag := "goedel-1"
%%%

A deduction system $`\mathcal{S}` is _complete_ iff it can prove or refute every sentence $`\sigma`.
Otherwise, $`\mathcal{S}` is _incomplete_.

{docstring LO.Entailment.Incomplete}

Let $`T` be a $`\Delta_1`-definable arithmetic theory, stronger than $`\mathsf{R}_0` and $`\Sigma_1`-sound.

```lean
variable
  (T : ArithmeticTheory)
  [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
```

# Representeation Theorem

Let $`P` be a r.e. set. There exists a formula $`\varphi_P(x)` such that $`n \in P \iff T \vdash \varphi_P(\overline{n})` for all $`n \in \mathbb{N}`.

{docstring LO.FirstOrder.Arithmetic.re_complete}

# First Incompleteness Theorem

Define a set $`D_T`, which satisfies $`\ulcorner\phi\urcorner \in D_T \iff T \vdash \lnot\phi(\ulcorner\phi\urcorner)`.
$`D_T` is a r.e. set, since the provability predicate of $`T` is $`\Sigma_1`-definable,
and the substitution function is $`\Delta_1`-definable.

```lean
def D : ℕ → Prop := fun φ : ℕ ↦
  IsSemiformula ℒₒᵣ 1 φ ∧
  T.Provable (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ)

lemma D_spec (φ : Semisentence ℒₒᵣ 1) :
    D T ⌜φ⌝ ↔ T ⊢ ∼φ/[⌜φ⌝] := by
  simp [D, ←provable_iff_provable, Sentence.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁,
    Semiformula.quote_def]

lemma D_re : REPred (D T) := by
  have : 𝚺₁-Predicate fun φ : ℕ ↦
    IsSemiformula ℒₒᵣ 1 φ ∧
    T.Provable (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ) := by
    definability
  exact re_iff_sigma1.mpr this
```

By the representeation theorem, there exists a $`\Sigma`-sentence $`\delta_T(x)`,
such that $`n \in D_T \iff T \vdash \delta_T(n)` for all $`n \in \mathbb{N}`.

```lean
noncomputable def δ : Semisentence ℒₒᵣ 1 :=
  codeOfREPred (D T)

lemma δ_spec (n : ℕ) : D T n ↔ T ⊢ (δ T)/[↑n] := by
  simpa [Semiformula.coe_subst_eq_subst_coe₁]
  using re_complete (D_re T)
```

Define sentence $`\pi_T`, defined as $`\delta_T(\ulcorner\delta_T\urcorner)`

```lean
noncomputable def π : Sentence ℒₒᵣ := (δ T)/[⌜δ T⌝]
```

By a simple inference, it can be shown that the provability of $`\pi_T` and the provability of its negation are equivalent.

```lean
lemma paradoxical : T ⊢ π T ↔ T ⊢ ∼π T := calc
  T ⊢ π T ↔ T ⊢ (δ T)/[⌜δ T⌝]  := by rfl
  _       ↔ D T ⌜δ T⌝          := by simpa using
                                     (δ_spec T ⌜δ T⌝).symm
  _       ↔ T ⊢ ∼(δ T)/[⌜δ T⌝] := D_spec T (δ T)
  _       ↔ T ⊢ ∼π T           := by rfl
```

Hence, $`\pi_T` and its negation are both unprovable from $`T`, since $`T` is consistent.

```lean
theorem unprovable : T ⊬ π T := by
  intro h
  have : T ⊢ ∼π T := (paradoxical T).mp h
  have : Inconsistent T :=
    inconsistent_of_provable_of_unprovable h this
  exact not_consistent_iff_inconsistent.mpr
    this inferInstance

theorem irrefutable : T ⊬ ∼π T := by
  intro h
  have : T ⊢ π T := (paradoxical T).mpr h
  have : Inconsistent T :=
    inconsistent_of_provable_of_unprovable this h
  exact not_consistent_iff_inconsistent.mpr
    this inferInstance
```

Therefore, we obtain the Gödel's first incompleteness theorem for $`\Delta_1`-theory stronger than $`\mathsf{R_0}` and $`\Sigma_1`-sound.

{docstring LO.FirstOrder.Arithmetic.incomplete}
