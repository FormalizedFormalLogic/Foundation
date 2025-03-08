# Arithmetics

In this formalization, we prefer developing arithmetic _model theoretic_, i.e.
show $T \models \sigma$ instead of $T \vdash \sigma$ (They are equivalent thanks to the completeness theorem.). This approach has several advantages:

1. In general, writing a formalized proof (in formalized system!) is very tedious. Meta-proofs, on the other hand, tend to be relatively concise.
2. Many definitions and proofs of logic and algebra in Mathlib can be used.
3. Metaprogramming can streamline the proof process (especially `definability`).
4. It is easy to extend predicates and functions. When adding predicates or functions, it is necessary to extend its language by _extension by definition_ in case of formalized proof, but not in model theoretic approach.

This procedure is done as follows.
Suppose we wish to prove that the totality of an exponential function can be proved in $\mathsf{I}\Sigma_1$.
First, the graph of the exponential function must be defined. This is achieved by the following two definitions.

1.  Semantic definition.
    ```lean
    def Exponential {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₀] :
        M → M → Prop
    ```
2.  Syntactic definition that expresses the semantic definition.

    ````lean
    def exponentialDef : 𝚺₀-Semisentence 2

        lemma Exponential.defined :
            𝚺₀-Relation (Exponential : M → M → Prop) via exponentialDef
        ```

    Then prove the totality.
    ````

```lean
theorem Exponential.total  {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₀] (x : M) : ∃ y, Exponential x y
```

Since `Exponential` and `Exponential.total` are defined in all the model of $\mathsf{I}\Sigma_1$,
`𝐈𝚺₁ ⊢! ∀' ∃' exponentialDef` is obtained by the completeness theorem. This was the result we wanted to achieve.

## Defined Predicates and Functions

|               Predicate/Function                | Notation                |                Defined in                |          Totality is proved in           | Complexity | Polynomial Bound |
| :---------------------------------------------: | :---------------------- | :--------------------------------------: | :--------------------------------------: | :--------: | :--------------: |
|                       $0$                       | `0`                     |                 $\empty$                 |                 $\empty$                 | $\Sigma_0$ |       $0$        |
|                       $1$                       | `1`                     |                 $\empty$                 |                 $\empty$                 | $\Sigma_0$ |       $1$        |
|                     $x + y$                     | `x + y`                 |                 $\empty$                 |                 $\empty$                 | $\Sigma_0$ |     $x + y$      |
|                   $x \cdot y$                   | `x * y`                 |                 $\empty$                 |                 $\empty$                 | $\Sigma_0$ |   $x \cdot y$    |
|                     $x = y$                     | `x = y`                 |                 $\empty$                 |                    -                     | $\Sigma_0$ |        -         |
|                     $x < y$                     | `x < y`                 |                 $\empty$                 |                    -                     | $\Sigma_0$ |        -         |
|                    $x \le y$                    | [`x ≤ y`]               |             $\mathsf{PA^-}$              |                    -                     | $\Sigma_0$ |        -         |
| $x \mathbin{\dot{-}} y$ (modified subtraction)  | [`x - y`]               |             $\mathsf{PA^-}$              |             $\mathsf{PA^-}$              | $\Sigma_0$ |       $x$        |
|              $x \mid y$ (devides)               | [`x ∣ y`]               |             $\mathsf{PA^-}$              |                    -                     | $\Sigma_0$ |        -         |
|                  $\min(x, y)$                   | `min x y`               |             $\mathsf{PA^-}$              |             $\mathsf{PA^-}$              | $\Sigma_0$ |       $x$        |
|                  $\max(x, y)$                   | `max x y`               |             $\mathsf{PA^-}$              |             $\mathsf{PA^-}$              | $\Sigma_0$ |     $x + y$      |
|             $\lfloor x / y \rfloor$             | [`x / y`]               |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ |       $x$        |
|        $\mathrm{rem}(x, y)$ (remainder)         | [`x % y`]               |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ |       $x$        |
|           $\lfloor \sqrt{x} \rfloor$            | [`√x`]                  |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ |       $x$        |
|                    $(x, y)$                     | [`⟪x, y⟫`]              |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ | $(x + y + 1)^2$  |
|     $\pi_1(x)$ (first inversion of pairing)     | [`π₁ x`]                |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ |       $x$        |
|    $\pi_2(x)$ (second inversion of pairing)     | [`π₂ x`]                |           $\mathsf{I_{open}}$            |           $\mathsf{I_{open}}$            | $\Sigma_0$ |       $x$        |
|                      $2^x$                      | [`exp x`]               |           $\mathsf{I}\Sigma_0$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       none       |
|           $\lfloor \log_2(x) \rfloor$           | [`log x`]               |           $\mathsf{I}\Sigma_0$           |           $\mathsf{I}\Sigma_0$           | $\Sigma_0$ |       $x$        |
|            $\| x \|$ (binary length)            | [`‖x‖`]                 |           $\mathsf{I}\Sigma_0$           |           $\mathsf{I}\Sigma_0$           | $\Sigma_0$ |       $x$        |
|                    $x \# y$                     | [`x # y`]               | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ |       none       |
|       $\mathrm{Nuon}(x)$ (number of ones)       | [`nuon x`]              | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ |       $x$        |
|         $x \in y$, $\mathrm{Bit}(x, y)$         | [`x ∈ y`]               |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Sigma_0$ |        -         |
|                    $\empty$                     | [`∅`]                   |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       $0$        |
|                 $x \subseteq y$                 | [`x ⊆ y`]               |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Sigma_0$ |        -         |
|                   $\bigcup x$                   | [`⋃ʰᶠ x`]               |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       none       |
|                   $x \cup y$                    | [`x ∪ y`]               |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |    $2(x + y)$    |
|                   $\bigcap x$                   | [`⋂ʰᶠ x`]               |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |        ?         |
|                   $x \cap y$                    | [`x ∩ y`]               |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       $x$        |
|        $x \times y$ (cartesian product)         | [`x ×ʰᶠ y`]             |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |        ?         |
|   $\mathrm{domain} (x)$ (domain of relation)    | [`domain x`]            |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |      $2 x$       |
|              $\mathrm{Mapping}(x)$              | [`IsMapping x`]         |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Sigma_0$ |        -         |
|                $\mathrm{Seq}(x)$                | [`Seq x`]               |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Sigma_0$ |        -         |
|      $\mathrm{lh}(x)$ (length of sequence)      | [`lh x`]                |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       $x$        |
| $x^\frown \braket{y}$ (concatation of sequence) | [`x ⁀' y`]              |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       none       |
|      $(x)_y$ ($y$-th element of sequence)       | [`znth x`]              |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_0$ |       $x$        |
|            $\mathrm{Semiterm}_x (y)$            | [`L.Semiterm x y`]      |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Delta_1$ |        -         |
|                  $t [\vec{w}]$                  | [`L.termSubst n m w t`] |           $\mathsf{I}\Sigma_1$           |           $\mathsf{I}\Sigma_1$           | $\Sigma_1$ |       none       |
|           $\mathrm{Semiformula}_x(y)$           | [`L.Semiformula x y`]   |           $\mathsf{I}\Sigma_1$           |                    -                     | $\Delta_1$ |        -         |

[`x ≤ y`]: https://formalizedformallogic.github.io/Foundation/docs/Logic/FirstOrder/Arith/PeanoMinus.html#LO.Arith.instLE_logic
[`x - y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/PeanoMinus.html#LO.Arith.sub
[`x ∣ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/PeanoMinus.html#LO.FirstOrder.Arith.dvd
[`x / y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.instDiv_arithmetization
[`x % y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.rem
[`√x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.sqrt
[`⟪x, y⟫`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.pair
[`π₁ x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%81
[`π₂ x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%82
[`exp x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaZero/Exponential/Exp.html#LO.Arith.Exponential
[`log x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.log
[`‖x‖`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.binaryLength
[`x # y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/OmegaOne/Basic.html#LO.Arith.instHash
[`nuon x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/OmegaOne/Nuon.html#LO.Arith.nuon
[`x ∈ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Bit.html#LO.Arith.Bit
[`∅`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instEmptyCollection_arithmetization
[`x ⊆ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instHasSubset_arithmetization
[`⋃ʰᶠ x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sUnion
[`x ∪ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.union
[`x ∩ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.inter
[`⋂ʰᶠ x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sInter
[`x ×ʰᶠ y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.product
[`domain x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.domain
[`IsMapping x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.IsMapping
[`Seq x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.Seq
[`lh x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.lh
[`x ⁀' y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.seqCons
[`znth x`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.znth
[`L.Semiterm x y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Metamath/Term/Basic.html#LO.Arith.Language.Semiterm
[`L.termSubst n m w t`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Metamath/Term/Functions.html#LO.Arith.Language.termSubst
[`L.Semiformula x y`]: https://formalizedformallogic.github.io/Arithmetization/docs/Arithmetization/ISigmaOne/Metamath/Formula/Basic.html#LO.Arith.Language.Semiformula
