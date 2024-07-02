# Gödel's Second Incompleteness Theorem

_These results are/will be included in [Arithmetization](https://github.com/iehality/Arithmetization/tree/master)._

Recall that inside $\mathsf{I}\Sigma_1$ we can do basic set theory and primitive recursion.

## Coding of Terms and Formulae

### Term
Define a class of (semi)terms using [fixpoint](https://iehality.github.io/lean4-logic/book/first_order/isigma1.html#fixpoint).
Define $T^n_C$ as follows.

$$
\begin{align*}
  u \in T^n_C &\iff
      && (\exists z < n)[u = \widehat{\#z}] \lor {}  \\
    & && (\exists x) [u = \widehat{\&x}] \lor {} \\
    & && (\exists k, f, v) [\mathrm{Func}_k(f) \land \mathrm{Seq}(v) \land k = \mathrm{lh}(v) \land (\forall i, z)[\braket{i, z} \in v \to z \in C] \land u = \widehat{f^k(v)}] \\
\end{align*}
$$

$\widehat{\bullet}$ is a quasi-quotation.
$$
\begin{align*}
  \widehat{\#z} &\coloneqq \braket{0, z} + 1 \\
  \widehat{\&x} &\coloneqq \braket{1, x} + 1 \\
  \widehat{f^k(v)} &\coloneqq \braket{2, f, k, v} + 1 \\
\end{align*}
$$

$T^n_C$ is $\Delta_1$ (if $C$ is a finite set) and monotone. Let $\mathrm{Semiterm}_n(t)$ be a fixpoint of $T^n_C$.
It is $\Delta_1$ since $T^n_C$ satisfies strong finiteness.

### Formula
Similarly, Define $F_C$:

$$
\begin{align*}
  u \in F_C &\iff
      && (\exists n, k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a sequence of $\mathrm{Semiterm}_n$ of length $k$} \land u = \widehat{R_n^k (v)}] \lor {}  \\
    & && (\exists n, k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a sequence of $\mathrm{Semiterm}_n$ of length $k$} \land u = \widehat{\lnot R_n^k (v)}] \lor {}  \\
    & && (\exists n) [u = \widehat{\top_n}] \lor {} \\
    & && (\exists n) [u = \widehat{\bot_n}] \lor {} \\
    & && (\exists n, p, q) [p \in C \land q \in C \land n = \mathrm{bv}(p) = \mathrm{bv}(q) \land u = \widehat{p \land_n q}] \lor {} \\
    & && (\exists n, p, q) [p \in C \land q \in C \land n = \mathrm{bv}(p) = \mathrm{bv}(q) \land u = \widehat{p \lor_n q}] \lor {} \\
    & && (\exists n, p) [p \in C \land n + 1 = \mathrm{bv}(p) \land u = \widehat{\forall_n p}] \lor {} \\
    & && (\exists n, p) [p \in C \land n + 1 = \mathrm{bv}(p) \land u = \widehat{\exists_n p}] 
\end{align*}
$$

The quasi-quotations are defined as follows:

$$
\begin{align*}
  \widehat{R^k_n(v)}       &\coloneqq \braket{n, 0, R, k, v} + 1\\
  \widehat{\lnot R^k_n(v)} &\coloneqq \braket{n, 1, R, k, v} + 1 \\
  \widehat{\top_n}         &\coloneqq \braket{n, 2, 0} + 1\\
  \widehat{\bot_n}         &\coloneqq \braket{n, 3, 0} + 1\\
  \widehat{p \land_n q}    &\coloneqq \braket{n, 4, p, q} + 1\\
  \widehat{p \lor_n q}     &\coloneqq \braket{n, 5, p, q} + 1\\
  \widehat{\forall_n p}    &\coloneqq \braket{n, 6, p} + 1\\
  \widehat{\exists_n p}    &\coloneqq \braket{n, 7, p} + 1\\
\end{align*}
$$

$$
  \mathrm{bv}(x) \coloneqq \pi_1(x - 1)
$$

$F_C$ is $\Delta_1$ and monotone. Let $\mathrm{UFormula}(t)$ be a fixpoint of $F_C$ and define

$$
\mathrm{Semiformula}_n(u) \iff \mathrm{UFormula}(u) \land n = \mathrm{bv}(u)
$$

$\mathrm{UFormula}(t)$ and $\mathrm{Semiormula}_n(t)$ are again $\Delta_1$ since $F_C$ satisfies strong finiteness.

### Negation

### Substitution

