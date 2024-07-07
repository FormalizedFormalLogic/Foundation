# Gödel's Second Incompleteness Theorem

_These results are/will be included in [Arithmetization](https://github.com/iehality/Arithmetization/tree/master)._

Recall that inside $\mathsf{I}\Sigma_1$ we can do basic set theory and primitive recursion.
Many inductive notions and functions on them are defined in $\Delta_1$ or $\Sigma_1$ using 
the [fixpoint construction](./isigma1.md#fixpoint).

## Coding of Terms and Formulae

### Term
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

### Inductively Defined Function on Semiterms



### Inductively Defined Function on Semiformulas

## Formalized Provability
Define $D_C$:

$$
\begin{align*}
  u \in D_C &\iff
    &&(\forall p \in u)[\mathrm{Semiformula}_0(p)] \land {} \\
    && [
    & (\exists k, R, v)[\widehat{R^k v} \in u \land \widehat{\lnot R^k v} \in u] \lor {} \\
    & && \widehat{\top_0} \in u \lor {}  \\
    & && (\exists p, q)[\widehat{p \land_0 q} \in u \land u \cup \{p\} \in C \land u \cup \{q\} \in C] \lor {}  \\
    & && (\exists p, q)[\widehat{p \lor_0 q} \in u \land u \cup \{p, q\} \in C] \lor {} \\
    & && (\exists p)[\widehat{\forall_0 p} \in u \land u^+ \cup \{p^+[\&0]\} \in C] \lor {} \\
    & && (\exists p, t)[\widehat{\exists_0 p} \in u \land u \cup \{p(t)\} \in C] \lor {} \\
    & && (\exists p)[u \cup \{p\} \in C \land u \cup \{\lnot p\} \in C]
     ]\end{align*}
$$
$p^+$ is a *shift* of a formula $p$. $u^+$ is a image of *shift* of $u$.
Take fixpoint $\mathrm{Derivable}(u)$.
Following holds for all finite set $\Gamma$.

$$
  \vdash_\mathsf{T} \Gamma \iff \mathsf{I}\Sigma_1 \vdash \mathrm{Derivable}(\ulcorner \Gamma \urcorner)
$$

- *Proof.* ($\Rightarrow$): Induction. ($\Leftarrow$): Use $\N \models \mathrm{Derivable}(\ulcorner \Gamma \urcorner)$ ∎

Let $T$ be a $\Sigma_1$-set of $\mathrm{Semiformula}_0$. Define the provability from $T$ as follows.

$$
  \Box_T(\varphi) \iff (\exists u)[u \subseteq T \land \mathrm{Derivable}(\lnot u \cup \{\varphi\})]
$$

$\Box_T (\varphi)$ is $\Sigma_1$. The following holds.

$$
  T \vdash \varphi \iff \mathsf{I}\Sigma_1 \vdash \Box_T(\ulcorner \varphi \urcorner) \\
  \mathsf{I}\Sigma_1 \vdash \Box_T(\ulcorner \varphi \to \psi \urcorner) \to \Box_T(\ulcorner \varphi\urcorner) \to \Box_T(\ulcorner \psi \urcorner)
$$

## Formalized $\Sigma_1$-Completeness
Working in $V$. Assume that $T$ is stronger than $\mathsf{PA}^-$.
For all $\Sigma_1$-formula $\varphi$ with $n$ variables, and $x_0, x_1, ..., x_{n-1} \in V$,

$$
  V \models \varphi[x_0, x_1, ..., x_{n-1}] \implies \Box_T(\ulcorner \varphi \urcorner[\overline{x_0}, \overline{x_1}, ..., \overline{x_{n-1}}])
$$
- *Proof*: meta-induction on $\varphi$.

$$
  \mathsf{I}\Sigma_1 \vdash \varphi \to \Box_T(\ulcorner \varphi \urcorner)
$$




