# Gödel's First Incompleteness Theorem

An outline of the formalized proof of Gödel's first incompleteness theorem.

## Definition

A deduction system $\mathcal{S}$ is _complete_ iff it can prove or refute every sentence $\sigma$.
Otherwise, $\mathcal{S}$ is _incomplete_.

```lean
def LO.System.Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ~f
```

## Theorem

$\Sigma_1$-sound and computable first-order theory, which is stronger than $\mathsf{PA}^-$, is incomplete.

```lean
theorem LO.FirstOrder.Arith.first_incompleteness
  (T : LO.FirstOrder.Theory ℒₒᵣ)
  [DecidablePred T]
  [𝐄𝐐 ≼ T]
  [𝐏𝐀⁻ ≼ T]
  [LO.FirstOrder.Arith.SigmaOneSound T]
  [LO.FirstOrder.Theory.Computable T] :
  ¬LO.System.Complete T
```

This theorem is proved two distinct approach.
- [G1 in `FirstIncompleteness.lean`](https://iehality.github.io/lean4-logic/docs/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.first_incompleteness)
- [G1 in `SelfReference.lean`](https://iehality.github.io/lean4-logic/docs/Logic/FirstOrder/Incompleteness/SelfReference.html#LO.FirstOrder.Arith.FirstIncompletenessBySelfReference.not_complete)

`FirstIncompleteness.lean` is computability theoretic proof, while `SelfReference.lean` uses a well-known self-referencial argument.

### G1 in `FirstIncompleteness.lean`
  
  Define a set of formulae with one variable.
  $$ D \coloneqq \{\varphi \mid T \vdash \lnot \varphi({\ulcorner \varphi \urcorner}) \} $$
  $D$ is r.e. since $T$ is computable. (one could use Craig's trick to weaken this condition to r.e., but I will not do that here.)

  By the representation theorem, there exists a $\Sigma_1$ formula $\rho(x)$ that represents $D$. i.e.,

  $$ T \vdash \rho({\ulcorner \varphi \urcorner}) \iff T \vdash \lnot \varphi({\ulcorner \varphi \urcorner})$$

  Let $\gamma := \rho({\ulcorner \rho \urcorner})$. The next follows immediately.

  $$ T \vdash \gamma \iff T \vdash \lnot \gamma $$

  Thus, as $T$ is consistent, $\gamma$ is undecidable from $T$.

### G1 in `SelfReference.lean`
  
  Since the substitution of a formula is computable, there exists an $\Sigma_1$ formula $\mathrm{ssbs}(x, y, z)$ that represents this:

  $$ T \vdash (\forall x)[\mathrm{ssbs}(x, {\ulcorner \varphi \urcorner}, {\ulcorner \psi \urcorner})
    \leftrightarrow x = {\ulcorner \varphi({\ulcorner \psi \urcorner}) \urcorner}] $$

  Define a sentence $\mathrm{fixpoint}_\theta$ for formula (with one variable) $\theta$ as follows.
  
  $$
    \begin{align*}
      \mathrm{fixpoint}_\theta
        &\coloneqq \mathrm{diag}_\theta(\ulcorner \mathrm{diag}_\theta \urcorner) \\
      \mathrm{diag}_\theta(x)
        &\coloneqq (\forall y)[\mathrm{ssbs}(y, x, x) \to \theta (y)]
    \end{align*}
  $$

  #### Fixpoint Lemma: $T \vdash \mathrm{fixpoint}_\theta \leftrightarrow \theta({\ulcorner \mathrm{fixpoint}_\theta \urcorner})$
  - _Proof._
    $$
      \begin{align*}
        \mathrm{fixpoint}_\theta
          &\equiv
            (\forall x)[
              \mathrm{ssbs}(
                x,
                {\ulcorner \mathrm{diag}_\theta \urcorner},
                {\ulcorner \mathrm{diag}_\theta \urcorner}) \to
              \theta (x)
              ] \\
          &\leftrightarrow 
            \theta(\ulcorner \mathrm{diag}_\theta(\ulcorner \mathrm{diag}_\theta \urcorner) \urcorner) \\
          &\equiv
            \theta(\ulcorner \mathrm{fixpoint}_\theta \urcorner)
      \end{align*}
    $$
    ∎
  
  Let $G := \mathrm{fixpoint}_{\lnot\mathrm{prov_T}(x)}$ (Gödel sentence; the sentence that states "This sentence is not provable"), 
  where $\mathrm{prov}_T(x)$ is a formula represents provability.

  Since $G$ is undecidable, this results in the incompleteness of $T$.
  - Assume that $T \vdash G$. $T \vdash \lnot \mathrm{prov}_T(\ulcorner G \urcorner)$ follows from the fixpoint lemma, 
    while $T \vdash \mathrm{prov}_T(\ulcorner G \urcorner)$ follows from the hypothesis. a contradiction.
  - Assume that $T \vdash \lnot G$. $T \vdash \mathrm{prov}_T(\ulcorner G \urcorner)$ follows from the fixpoint lemma,
    and $T \vdash G$ follows. a contradiction.

## About Second Theorem

To prove the second incompleteness theorem, as outlined in Gödel's original paper, one can derive it by proving the first incompleteness theorem again within arithmetic.
Although this fact has not yet been formalized in this project.
These efforts are being undertaken in a separated repository [iehality/Arithmetization](https://github.com/iehality/Arithmetization).

Notably, the formalization of the second incompleteness theorem has already been accomplished by L. C. Paulson in Isabelle.
However, owing to the technical simplicity for coding and others. this formalization is on *hereditarily finite sets* and not on arithmetic.
- [L. C. Paulson, "A machine-assisted proof of Gödel's incompleteness theorems for the theory of hereditarily finite sets"](https://www.repository.cam.ac.uk/items/bda52431-26e0-4e86-8d63-409bcedd4617)
- [Isabelle AFP](https://www.isa-afp.org/entries/Incompleteness.html)
