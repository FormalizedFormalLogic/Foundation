# Gödel's First Incompleteness Theorem

A deduction system $\mathcal{S}$ is _complete_ iff it can prove or refute every sentence $\sigma$.
Otherwise, $\mathcal{S}$ is _incomplete_.

```lean
def System.Complete {F S} [System F S] [LogicalConnective F] (𝓢 : S) : Prop :=
    ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ~f
```
- [System.Complete](https://formalizedformallogic.github.io/Incompleteness/docs/Logic/Logic/System.html#LO.System.Complete)

## Theorem

Let $T$ be a $\Delta_1$-definable arithmetic theory, stronger than $\mathsf{R}_0$ and $\Sigma_1$-sound.

### Representeation Theorem

#### Theorem: Let $P$ be a r.e. set. There exists a formula $\varphi_P(x)$ such that $n \in P \iff T \vdash \varphi_P(\overline{n})$ for all $n \in \mathbb{N}$.

```lean
lemma re_complete
    [𝐑₀ ≼ T] [Sigma1Sound T]
    {p : ℕ → Prop} (hp : RePred p) {x : ℕ} :
    p x ↔ T ⊢! (codeOfRePred p)/[‘↑x’] 
```
- [re_complete](https://formalizedformallogic.github.io/Foundation/doc/Foundation/FirstOrder/R0/Representation.html#LO.FirstOrder.Arithmetic.re_complete)

### Main Theorem

#### Theorem: $\Sigma_1$-sound and $\Delta_1$-definable first-order theory, which is stronger than $\mathsf{R_0}$, is incomplete.

- _Proof._

  Define a set of formulae with one variable.
  $$ D \coloneqq \{\varphi \mid T \vdash \lnot \varphi({\ulcorner \varphi \urcorner}) \} $$
    $D$ is r.e. since $T$ is $\Delta_1$-definable. (one could use Craig's trick to weaken this condition to $\Sigma_1$, but I will not do that here.)
  
  By the representation theorem, there exists a $\Sigma_1$ formula $\rho(x)$ that represents $D$. i.e.,
  
  $$ T \vdash \rho({\ulcorner \varphi \urcorner}) \iff T \vdash \lnot \varphi({\ulcorner \varphi \urcorner})$$
  
  Let $\gamma := \rho({\ulcorner \rho \urcorner})$. The next follows immediately.
  
  $$ T \vdash \gamma \iff T \vdash \lnot \gamma $$
  
  Thus, as $T$ is consistent, $\gamma$ is undecidable from $T$. ∎

```lean
theorem goedel_first_incompleteness
  (T : ArithmeticTheory) [𝐑₀ ≼ T] [Sigma1Sound T] [T.Δ₁] :
  ¬System.Complete T
```
- [goedel_first_incompleteness](https://formalizedformallogic.github.io/Foundation/doc/Foundation/FirstOrder/Incompleteness/First.html#LO.R0.goedel_first_incompleteness)