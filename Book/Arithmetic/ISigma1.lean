import Book.Init

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true

open Verso.Code.External

#doc (Manual) "ISigma1" =>
%%%
tag := "first-order-isigma1"
%%%

# Exponential

It is proved that the graph of exponential is definable by $`\Sigma_0`-formula,
and their inductive properties are provable in $`\mathsf{I}\Sigma_0`.
In $`\mathsf{I}\Sigma_1`, we can further prove their entireness.

# Theory of Hereditary Finite Sets

Weak theory of sets in $`V_\omega` (Hereditary Finite Sets) can be developed
inside $`\mathsf{I}\Sigma_1` using Ackermann coding and bit predicate.
Hereafter, we will use the notation $`i \in a` in the sense of bit predicate:

-- TODO: LO.Arith.mem_iff_bit

The following comprehension holds.

{docstring LO.ISigma1.finset_comprehension₁}

The basic concepts of set theory, such as union, inter, cartesian product, and mapping, etc. are defined.

## Seq

$`\mathrm{Seq}(s)` iff $`s` is a mapping and its domain is $`[0, l)` for some $`l`.

-- TODO: LO.ISigma1.Seq

# Primitive Recursion

Let $`f(\vec v)`, $`g(\vec{v}, x, z)` be a $`\Sigma_1`-function.
There is a $`\Sigma_1`-function $`\mathsf{PR}_{f,g}(\vec{v}, u)` such that:

```math
\begin{align*}
  \mathsf{PR}_{f,g}(\vec{v}, 0) &= f(\vec{v}) \\
  \mathsf{PR}_{f,g}(\vec{v}, u + 1) &= g(\vec{v}, u, \mathsf{PR}_{f,g}(\vec{v}, u))
\end{align*}
```

{docstring LO.ISigma1.PR.Blueprint}

{docstring LO.ISigma1.PR.Construction}

{docstring LO.ISigma1.PR.Construction.result}

{docstring LO.ISigma1.PR.Construction.result_zero}

{docstring LO.ISigma1.PR.Construction.result_succ}

# Fixpoint

Let $`\Phi_C(\vec{v}, x)` be a predicate, which takes a _class_ $`C` as a parameter.
Then there is a $`\Sigma_1`-predicate $`\mathsf{Fix}_{\Phi}(\vec{v}, x)` such that

```math
  \mathsf{Fix}_\Phi(\vec{v}, x) \iff \Phi_{\{z \mid \mathsf{Fix}_\Phi(\vec{v}, z)\}} (\vec{v}, x)
```

if $`\Phi` satisfies following conditions:

1 $`\Phi` is $`\Delta_1`-definable if $`C` is a set. i.e.,
   a predicate $`(c, \vec{v}, x) \mapsto \Phi_{\{z \mid \mathrm{Bit}(z, c)\}}(\vec{v}, x)` is $`\Delta_1`-definable.
2 _Monotone_: $`C \subseteq C'` and $`\Phi_C(\vec{v}, x)` implies $`\Phi_{C'}(\vec{v}, x)`.
3 _Finite_: $`\Phi_C (\vec{v}, x)` implies the existence of a $`m` s.t. $`\Phi_{\{z \in C \mid z < m\}} (\vec{v}, x)`.

{docstring LO.ISigma1.Fixpoint.Blueprint}

{docstring LO.ISigma1.Fixpoint.Construction}

{docstring LO.ISigma1.Fixpoint.Construction.Finite}

{docstring LO.ISigma1.Fixpoint.Construction.Fixpoint}

{docstring LO.ISigma1.Fixpoint.Construction.case}

$`\mathsf{Fix}_\Phi(\vec v, x)` is $`\Delta_1` if $`\Phi` satisfies strong finiteness:

{docstring LO.ISigma1.Fixpoint.Construction.StrongFinite}

Also structural induction holds.

{docstring LO.ISigma1.Fixpoint.Construction.induction}
