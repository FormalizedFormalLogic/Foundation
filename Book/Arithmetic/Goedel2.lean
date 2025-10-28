import Book.Init

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true
set_option linter.unusedSectionVars false

open LO Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Bootstrapping InternalArithmetic

#doc (Manual) "Gödel's Second Incompleteness Theorem" =>
%%%
tag := "goedel-2"
%%%

Recall that inside $`\mathsf{I}\Sigma_1` we can do basic set theory and primitive recursion.
Many inductive notions and functions on them are defined in $`\Delta_1` or $`\Sigma_1` using
the fixedpoint construction.

We work inside an arbitrary model $`V` of $`\mathsf{I}\Sigma_1`.

# Coding of Terms and Formulae

## Term
Define $`T_C` as follows.

```math
\begin{align*}
  u \in T_C &\iff
      && (\exists z)[u = \widehat{\#z}] \lor {}  \\
    & && (\exists x) [u = \widehat{\&x}] \lor {} \\
    & && (\exists k, f, v) [\mathrm{Func}_k(f) \land \mathrm{Seq}(v)
      \land k = \mathrm{lh}(v) \land (\forall i, z)[\braket{i, z} \in v \to z \in C] \land u = \widehat{f^k(v)}] \\
\end{align*}
```

$`\widehat{\bullet}` is a quasi-quotation..

```math
\begin{align*}
  \text{bounded variable: }&& \widehat{\#z} &\coloneqq \braket{0, z} + 1 \\
  \text{free variable: }&&\widehat{\&x} &\coloneqq \braket{1, x} + 1 \\
  \text{function: }&&\widehat{f^k(v)} &\coloneqq \braket{2, f, k, v} + 1 \\
\end{align*}
```

$`T_C` is $`\Delta_1` (if $`C` is a finite set) and monotone. Let $`\mathrm{UTerm}(t)` be a fixedpoint of $`T_C`.
It is $`\Delta_1` since $`T_C` satisfies strong finiteness.
Define the function $`\mathrm{termBV}(t)` inductively on $`\mathrm{UTerm}` meaning
the largest bounded variable $`+1` that appears in the term.
Define $`\mathrm{Semiterm}(n, t) := \mathrm{UTerm}(t) \land \mathrm{termBV}(t) \le n`.

{docstring LO.FirstOrder.Arithmetic.Bootstrapping.IsSemiterm}

## Formula

Similarly, Define $`F_C`:

```math
\begin{align*}
  u \in F_C &\iff
      && (\exists k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a list of $\mathrm{UTerm}$ of length $k$} \land u = \widehat{R^k (v)}] \lor {}  \\
    & && (\exists k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a list of $\mathrm{UTerm}$ of length $k$} \land u = \widehat{\lnot R^k (v)}] \lor {}  \\
    & && [u = \widehat{\top}] \lor {} \\
    & && [u = \widehat{\bot}] \lor {} \\
    & && (\exists p \in C, q \in C) [u = \widehat{p \land q}] \lor {} \\
    & && (\exists p \in C, q \in C) [u = \widehat{p \lor q}] \lor {} \\
    & && (\exists p \in C) [u = \widehat{\forall p}] \lor {} \\
    & && (\exists p \in C) [u = \widehat{\exists p}]
\end{align*}
```

```math
\begin{align*}
  \widehat{R^k(v)}       &\coloneqq \braket{0, R, k, v} + 1\\
  \widehat{\lnot R^k(v)} &\coloneqq \braket{1, R, k, v} + 1 \\
  \widehat{\top}         &\coloneqq \braket{2, 0} + 1\\
  \widehat{\bot}         &\coloneqq \braket{3, 0} + 1\\
  \widehat{p \land q}    &\coloneqq \braket{4, p, q} + 1\\
  \widehat{p \lor q}     &\coloneqq \braket{5, p, q} + 1\\
  \widehat{\forall p}    &\coloneqq \braket{6, p} + 1\\
  \widehat{\exists p}    &\coloneqq \braket{7, p} + 1\\
\end{align*}
```

$`F_C` is $`\Delta_1` and monotone. Let $`\mathrm{UFormula}(p)` be a fixedpoint of $`F_C` and define

```
\mathrm{Semiformula}(n, p) \iff \mathrm{UFormula}(p) \land \mathrm{bv}(p) \le n
```

{docstring LO.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula}

The function $`\mathrm{bv}(p)` is defined inductively on $`\mathrm{UFormula}` meaning the largest bounded variable $`+1` that appears in the formula.

$`\mathrm{UFormula}(p)` and $`\mathrm{Semiormula}(n, p)` are again $`\Delta_1` since $`F_C` satisfies strong finiteness.

{docstring LO.FirstOrder.Arithmetic.Bootstrapping.IsUFormula}

# Formalized Provability

Let $`T` be $`\Delta_1`-definable theory.
Define $`D_C`:

```math
\begin{align*}
  d \in D_C &\iff
    &&(\forall p \in \mathrm{sqt}(d))[\mathrm{Semiformula}(0, p)] \land {} \\
    && [
    & (\exists s, p)[d = \widehat{\text{AXL}(s, p)} \land p \in s \land \hat\lnot p \in s] \lor {} \\
    & && (\exists s)[d = \widehat{\top\text{-INTRO}(s)} \land \widehat{\top} \in s] \lor {}  \\
    & && (\exists s, p, q)(\exists d_p, d_q \in C)[
      d = \widehat{\land\text{-INTRO} (s, p, q, d_p, d_q)} \land
      \widehat{p \land q} \in s \land
      \mathrm{sqt}(d_p) = s \cup \{p\} \land \mathrm{sqt}(d_q) = s \cup \{q\}] \lor {}  \\
    & && (\exists s, p, q)(\exists d \in C)[
      d = \widehat{\lor\text{-INTRO}(s, p,q,d)} \land
      \widehat{p \lor q} \in s \land \mathrm{sqt}(d) = s \cup \{p, q\}] \lor {} \\
    & && (\exists s, p)(\exists d \in C)[
      d = \widehat{\forall\text{-INTRO}(s, p, d)} \land
      \widehat{\forall p} \in s \land \mathrm{sqt}(d) = s^+ \cup \{p^+[\&0]\}] \lor {} \\
    & && (\exists s, p, t)(\exists d \in C)[
      d = \widehat{\exists\text{-INTRO}(s, p, t, d)} \land
      \widehat{\exists p} \in s \land \mathrm{sqt}(d) = s \cup \{p(t)\}] \lor {} \\
    & && (\exists s)(\exists d' \in C)[
      d = \widehat{\mathrm{WK}(s, d')} \land
      s \supseteq \mathrm{sqt}(d') ] \\
    & && (\exists s)(\exists d' \in C)[
      d = \widehat{\mathrm{SHIFT}(s, d')} \land
      s = \mathrm{sqt}(d')^+ ] \\
    & && (\exists s, p)(\exists d_1, d_2 \in C)[
      d = \widehat{\mathrm{CUT}(s, p, d_1, d_2)} \land
      \mathrm{sqt}(d_1) = s \cup \{p\} \land \mathrm{sqt}(d_2) = s \cup \{\lnot p\}] \\
    & && (\exists s, p)[
      d = \widehat{\mathrm{ROOT}(s, p)} \land
      p \in s \land p \in T ]
     ]\end{align*}
```

```math
\begin{align*}
  \widehat{\text{AXL}(s, p)}       &\coloneqq \braket{s, 0, p} + 1\\
  \widehat{\top\text{-INTRO}(s)} &\coloneqq \braket{s, 1, 0} + 1 \\
  \widehat{\land\text{-INTRO}(s, p, q, d_p, d_q)}         &\coloneqq \braket{s,2, p, q, d_p, d_q} + 1\\
  \widehat{\lor\text{-INTRO}(s, p, q, d)}         &\coloneqq \braket{s, 3,p, q, d} + 1\\
  \widehat{\forall\text{-INTRO}(s, p, d)}    &\coloneqq \braket{s, 4, p, d} + 1\\
  \widehat{\exists\text{-INTRO}(s, p, t, d)}     &\coloneqq \braket{s, 5, p, t, d} + 1\\
  \widehat{\text{WK}(s, d)}    &\coloneqq \braket{s, 6, d} + 1\\
  \widehat{\text{SHIFT}(s, d)}    &\coloneqq \braket{s, 7, d} + 1\\
  \widehat{\text{CUT}(s, p, d_1, d_2)}    &\coloneqq \braket{s, 8, p, d_1, d_2} + 1\\
  \widehat{\text{ROOT}(s, p)}    &\coloneqq \braket{s, 9, p} + 1 \\
  \mathrm{sqt}(d) &\coloneqq \pi_1(d - 1)
\end{align*}
```

$`p^+` is a *shift* of a formula $`p`. $`s^+` is a image of *shift* of $`s`.
Take fixedpoint $`\mathrm{Derivation}_T(d)`.

```math
\begin{align*}
  \mathrm{Derivable}_T(\Gamma) &\coloneqq (\exists d)[\mathrm{Derivation}_T(d) \land \mathrm{sqt}(d) = \Gamma] \\
  \mathrm{Provable}_T(p) &\coloneqq \mathrm{Derivable}_T(\{p\})
\end{align*}
```

{docstring LO.FirstOrder.Theory.Derivable}

{docstring LO.FirstOrder.Theory.Provable}

{docstring LO.FirstOrder.Theory.Proof}

Following holds for all formula (not coded one) $`\varphi` and finite set $`\Gamma`.

$`\N \models \mathrm{Provable}_T(\ulcorner \varphi \urcorner) \implies T \vdash \varphi`

{docstring LO.FirstOrder.Theory.Provable.sound}

Now assume that $`U` is a theory of arithmetic stronger than $`\mathsf{R_0}` and
$`T` be a theory of arithmetic stronger than $`\mathsf{I}\Sigma_1`.
The following holds, thanks to the completeness theorem.

1 $`U \vdash \sigma \iff T \vdash \mathrm{Provable}_U(\ulcorner \sigma \urcorner)`

{docstring LO.FirstOrder.Arithmetic.provable_complete}

2 $`T \vdash \mathrm{Provable}_U(\ulcorner \sigma \to \pi \urcorner) \to \mathrm{Provable}_U(\ulcorner \sigma \urcorner) \to \mathrm{Provable}_U(\ulcorner \pi \urcorner)`

{docstring LO.FirstOrder.Arithmetic.provable_D2}

3 $`T \vdash \mathrm{Provable}_U(\ulcorner \sigma \urcorner) \to \mathrm{Provable}_U(\ulcorner \mathrm{Provable}_U(\ulcorner \sigma \urcorner) \urcorner)`

{docstring LO.FirstOrder.Arithmetic.provable_D3}

# Second Incompleteness Theorem

Assume that $`T` is $`\Delta_1`-definable and stronger than $`\mathsf{I}\Sigma_1`.

```lean
section

variable (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T]
```

## Fixed-point Lemma

Since the substitution is $`\Sigma_1`, There is a formula $`\mathrm{ssnum}(y, p, x)`
such that, for all formula $`\varphi` with only one variable and $`x, y \in V`,

```math
  \mathrm{ssnum}(y, {\ulcorner \varphi \urcorner}, x) \iff y = \ulcorner \varphi(\overline{x}) \urcorner
```

holds. (overline $`\overline{\bullet}` denotes the (formalized) numeral of $`x`)

Define a sentence $`\mathrm{fixedpoint}_\theta` for formula (with one variable) $`\theta` as follows.

```math
  \begin{align*}
    \mathrm{fixedpoint}_\theta
      &\coloneqq \mathrm{diag}_\theta(\overline{\ulcorner \mathrm{diag}_\theta \urcorner}) \\
    \mathrm{diag}_\theta(x)
      &\coloneqq (\forall y)[\mathrm{ssnum}(y, x, x) \to \theta (y)]
  \end{align*}
```

```lean
namespace Book

noncomputable def diag (θ : Semisentence ℒₒᵣ 1) :
  Semisentence ℒₒᵣ 1 := “x. ∀ y, !ssnum y x x → !θ y”

noncomputable def fixedpoint (θ : Semisentence ℒₒᵣ 1) :
  Sentence ℒₒᵣ := (Book.diag θ)/[⌜Book.diag θ⌝]
```

By simple reasoning, it can be checked that f satisfies the following:

```math
  T \vdash \mathrm{fixedpoint}_\theta \leftrightarrow \theta({\ulcorner \mathrm{fixedpoint}_\theta \urcorner})
```

```lean
theorem diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢ fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝] :=
  haveI : 𝗘𝗤 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁)
    inferInstance inferInstance
  provable_of_models _ _
  fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝗜𝚺₁ :=
      ModelsTheory.of_provably_subtheory
      V 𝗜𝚺₁ T inferInstance
    suffices
      V ⊧/![] (fixedpoint θ) ↔ V ⊧/![⌜fixedpoint θ⌝] θ by
      simpa [models_iff, Matrix.constant_eq_singleton]
    let t : V := ⌜diag θ⌝
    have ht : substNumeral t t = ⌜fixedpoint θ⌝ := by
      simp [t, fixedpoint, substNumeral_app_quote]
    calc
      V ⊧/![] (fixedpoint θ)
    _ ↔ V ⊧/![t] (diag θ)         := by
      simp [fixedpoint, Matrix.constant_eq_singleton, t]
    _ ↔ V ⊧/![substNumeral t t] θ := by
      simp [diag, Matrix.constant_eq_singleton]
    _ ↔ V ⊧/![⌜fixedpoint θ⌝] θ   := by simp [ht]

end Book
```

## Main Theorem

Let $`T` be a $`\Delta_1`-theory, which is stronger than $`\mathsf{I}\Sigma_1`.

```lean
namespace Book

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
```

We will use $`\square \varphi` to denote $`\mathrm{Provable}(\ulcorner\varphi\urcorner)`.
Define Gödel sentence $`\mathsf{G}`, as $`\mathrm{fixedpoint}_{\lnot\mathrm{Provable}_T(x)}` using fixed-point theorem, satisfies

```math
  T \vdash \mathsf{G} \leftrightarrow \lnot \mathrm{Provable}(\ulcorner\mathsf{G}\urcorner)
```

```lean
local prefix:max "□" => T.provabilityPred

noncomputable def gödel : Sentence ℒₒᵣ :=
  Book.fixedpoint (∼T.provable)

local notation "𝗚" => gödel T

variable {T}

lemma gödel_spec : T ⊢ 𝗚 ⭤ ∼□𝗚 := by
  simpa using Book.diagonal T (∼T.provable)
```

Gödel sentence is undecidable, i.e., $`T \nvdash \mathsf{G}` if $`T` is consistent,

```lean
lemma gödel_unprovable [Entailment.Consistent T] :
    T ⊬ 𝗚 := by
  intro h
  have hp : T ⊢ □𝗚 :=
    weakening inferInstance (provable_D1 h)
  have hn : T ⊢ ∼□𝗚 :=
    K!_left gödel_spec ⨀ h
  exact not_consistent_iff_inconsistent.mpr
    (inconsistent_of_provable_of_unprovable hp hn)
    inferInstance
```

And $`T \nvdash \lnot\mathsf{G}` if $`\mathbb{N} \models T`.

```lean
lemma gödel_irrefutable [ℕ ⊧ₘ* T] : T ⊬ ∼𝗚 := fun h ↦ by
  have : T ⊢ □𝗚 :=
    CN!_of_CN!_left (K!_right gödel_spec) ⨀ h
  have : T ⊢ 𝗚 := provable_sound this
  exact not_consistent_iff_inconsistent.mpr
    (inconsistent_of_provable_of_unprovable this h)
    (Sound.consistent_of_satisfiable
      ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩)
```

Define formalized consistent statement $`\mathrm{Con}_T` as $`\lnot\mathrm{Provable}_T(\ulcorner \bot \urcorner)`:

```lean
variable (T)

noncomputable def consistent : Sentence ℒₒᵣ := ∼□⊥

local notation "𝗖𝗼𝗻" => consistent T
```

And, surprisingly enough, it can be proved that Gödel sentence $`\mathsf{G}` is equivalent to the consistency statement.

```lean
variable {T}

open Entailment FiniteContext

lemma consistent_iff_goedel : T ⊢ 𝗖𝗼𝗻 ⭤ 𝗚 := by
  apply E!_intro
  · have bew_G : [∼𝗚] ⊢[T] □𝗚 :=
      deductInv'! <| CN!_of_CN!_left <| K!_right gödel_spec
    have bew_not_bew_G : [∼𝗚] ⊢[T] □(∼□𝗚) := by
      have : T ⊢ □(𝗚 ➝ ∼□𝗚) :=
        weakening inferInstance
        <| provable_D1 <| K!_left gödel_spec
      exact provable_D2_context (of'! this) bew_G
    have bew_bew_G : [∼𝗚] ⊢[T] □□𝗚 :=
      provable_D3_context bew_G
    have : [∼𝗚] ⊢[T] □⊥ :=
      provable_D2_context
        (provable_D2_context
          (of'! <| weakening inferInstance
          <| provable_D1 CNC!) bew_not_bew_G)
        bew_bew_G
    exact CN!_of_CN!_left (deduct'! this)
  · have : [□⊥] ⊢[T] □𝗚 := by
      have : T ⊢ □(⊥ ➝ 𝗚) :=
        weakening inferInstance <| provable_D1 efq!
      exact provable_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T] ∼𝗚 :=
      of'!
        (CN!_of_CN!_right <| K!_left <| gödel_spec)
      ⨀ this
    exact CN!_of_CN!_right (deduct'! this)
```

Finally, combined with the fact that $`\mathsf{G}` is independent,
we can prove that the consistency statement is also independent.

```lean
theorem consistent_unprovable [Consistent T] :
    T ⊬ 𝗖𝗼𝗻 := fun h ↦
  gödel_unprovable <| K!_left consistent_iff_goedel ⨀ h

theorem inconsistent_unprovable [ℕ ⊧ₘ* T] :
    T ⊬ ∼𝗖𝗼𝗻 := fun h ↦
  gödel_irrefutable
  <| contra! (K!_right consistent_iff_goedel) ⨀ h
```

{docstring LO.FirstOrder.Arithmetic.consistent_unprovable}

{docstring LO.FirstOrder.Arithmetic.inconsistent_independent}
