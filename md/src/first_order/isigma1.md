# Theory $\mathsf{I}\Sigma_1$

_These results are included in [Arithmetization](https://github.com/iehality/Arithmetization/tree/master)._

### Exponential

It is proved that the graph of exponential is definable by $\Sigma_1$-formula,
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
theorem finset_comprehension₁ [M ⊧ₘ* 𝐈𝚺₁] {P : M → Prop} (hP : (Γ, 1)-Predicate P) (a : M) :
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