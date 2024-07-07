# Theory $\mathsf{I}\Sigma_1$

_These results are included in [Arithmetization](https://github.com/iehality/Arithmetization/tree/master)._

### Exponential

It is proved that the graph of exponential is definable by $\Sigma_0$-formula,
and their inductive properties are provable in $\mathsf{I}\Sigma_0$.
In $\mathsf{I}\Sigma_1$, we can further prove their entireness.

## Theory of Hereditary Finite Sets in $\mathsf{I}\Sigma_1$

Weak theory of sets in $V_\omega$ (Hereditary Finite Sets) can be developed inside $\mathsf{I}\Sigma_1$ using Ackermann coding and bit predicate. Hereafter, we will use the notation $i \in a$ in the sense of bit predicate:

```lean
lemma mem_iff_bit [M ⊧ₘ* 𝐈𝚺₁] {i a : M} : i ∈ a ↔ Bit i a
```

- [LO.FirstOrder.Arith.Model.mem_iff_bit](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.FirstOrder.Arith.Model.mem_iff_bit)

The following comprehension holds.

```lean
theorem finset_comprehension₁ [M ⊧ₘ* 𝐈𝚺₁]
    {P : M → Prop} (hP : (Γ, 1)-Predicate P) (a : M) :
    ∃ s < exp a, ∀ i < a, i ∈ s ↔ P i
```
- [LO.FirstOrder.Arith.Model.finset_comprehension₁](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.FirstOrder.Arith.Model.finset_comprehension%E2%82%81)

The basic concepts of set theory, such as [union](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.FirstOrder.Arith.Model.union), [inter](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.FirstOrder.Arith.Model.inter), 
[cartesian product](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.FirstOrder.Arith.Model.product),
and [mapping](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.FirstOrder.Arith.Model.IsMapping), etc. are defined.

### Seq
$\mathrm{Seq}(s)$ iff $s$ is a mapping and its domain is $[0, l)$ for some $l$.

```lean
def Seq [M ⊧ₘ* 𝐈𝚺₁] (s : M) : Prop := IsMapping s ∧ ∃ l, domain s = under l
```
- [LO.FirstOrder.Arith.Model.Seq](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.FirstOrder.Arith.Model.Seq)

### Primitive Recursion

Let $f(\vec v)$, $g(\vec{v}, x, z)$ be a $\Sigma_1$-function.
There is a $\Sigma_1$-function $\mathsf{PR}_{f,g}(\vec{v}, u)$ such that:

$$
\begin{align*}
  \mathsf{PR}_{f,g}(\vec{v}, 0) &= f(\vec{v}) \\
  \mathsf{PR}_{f,g}(\vec{v}, u + 1) &= g(\vec{v}, u, \mathsf{PR}_{f,g}(\vec{v}, u))
\end{align*}
$$

```lean
structure Formulae (k : ℕ) where
  zero : 𝚺₁-Semisentence (k + 1)
  succ : 𝚺₁-Semisentence (k + 3)

structure Construction {k : ℕ} (p : Formulae k) where
  zero : (Fin k → M) → M
  succ : (Fin k → M) → M → M → M
  zero_defined : DefinedFunction zero p.zero
  succ_defined : DefinedFunction (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ

variable {k : ℕ} {p : Formulae k} (c : Construction M p) (v : Fin k → M)

def Construction.result (u : M) : M

theorem Construction.result_zero :
    c.result v 0 = c.zero v

theorem Construction.result_succ (u : M) :
    c.result v (u + 1) = c.succ v u (c.result v u)
```
- [Formulae](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/PRF.html#LO.FirstOrder.Arith.Model.PR.Formulae), [Construction](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/PRF.html#LO.FirstOrder.Arith.Model.PR.Construction), [Construction.result](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/PRF.html#LO.FirstOrder.Arith.Model.PR.Construction.result), [Construction.result_zero](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/PRF.html#LO.FirstOrder.Arith.Model.PR.Construction.result_zero), [Construction.result_succ](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/PRF.html#LO.FirstOrder.Arith.Model.PR.Construction.result_succ)

### Fixpoint

Let $\Phi_C(\vec{v}, x)$ be a predicate, which takes a *class* $C$ as a parameter.
Then there is a $\Sigma_1$-predicate $\mathsf{Fix}_{\Phi}(\vec{v}, x)$ such that

$$
  \mathsf{Fix}_\Phi(\vec{v}, x) \iff \Phi_{\{z \mid \mathsf{Fix}_\Phi(\vec{v}, z)\}} (\vec{v}, x)
$$

if $\Phi$ satisfies following conditions:

1.  $\Phi$ is $\Delta_1$-definable if $C$ is a set. i.e.,
    a predicate $(c, \vec{v}, x) \mapsto \Phi_{\{z \mid \mathrm{Bit}(z, c)\}}(\vec{v}, x)$ is $\Delta_1$-definable.
2.  *Monotone*: $C \subseteq C'$ and $\Phi_C(\vec{v}, x)$ implies $\Phi_{C'}(\vec{v}, x)$.
3. *Finite*: $\Phi_C (\vec{v}, x)$ implies the existence of a $m$ s.t. $\Phi_{\{z \in C \mid z < m\}} (\vec{v}, x)$.

```lean
structure Blueprint (k : ℕ) where
  core : 𝚫₁-Semisentence (k + 2)

structure Construction (φ : Blueprint k) where
  Φ : (Fin k → M) → Set M → M → Prop
  defined : Arith.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set M} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

class Construction.Finite (c : Construction M φ) where
  finite {C : Set M} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

variable {k : ℕ} {φ : Blueprint k} (c : Construction M φ) [Finite c] (v : Fin k → M)

def Construction.Fixpoint (x : M) : Prop

theorem Construction.case :
    c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x
```
- [Blueprint](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.Arith.Fixpoint.Blueprint), [Construction](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.FirstOrder.Arith.Model.Fixpoint.Construction), [Construction.Finite](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.Arith.Fixpoint.Construction.Finite), [Construction.Fixpoint](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.FirstOrder.Arith.Model.Fixpoint.Construction.Fixpoint), [Construction.case](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.FirstOrder.Arith.Model.Fixpoint.Construction.case)

$\mathsf{Fix}_\Phi(\vec v, x)$ is $\Delta_1$ if $\Phi$ satisfies strong finiteness:
```lean
class Construction.StrongFinite (c : Construction M φ) where
  strong_finite {C : Set M} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x
```
- [StrongFinite](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.Arith.Fixpoint.Construction.StrongFinite)

Also structural induction holds.

```lean
theorem Construction.induction [c.StrongFinite]
    {P : M → Prop} (hP : (Γ, 1)-Predicate P)
    (H : ∀ C : Set M, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x
```
- [LO.Arith.Fixpoint.Construction.induction](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Fixpoint.html#LO.Arith.Fixpoint.Construction.induction)