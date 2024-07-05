# Theories of Arithmetics

|                            | Notation | Description                                       |                                                               |
| :-:                        | :-:      | :--                                               | :--                                                           |
| $\mathsf{PA^-}$            | `𝐏𝐀⁻`    | Finitely axiomatized fragment of $\mathsf{PA}$    |                                                               |
| $\mathsf{I_{open}}$        | `𝐈open`  | $\mathsf{PA}^-$ + Induction of open formula       |                                                               |
| $\mathsf{I}\Sigma_0$       | `𝐈𝚺₀`    | $\mathsf{PA}^-$ + Induction of $\Sigma_0$ formula | [Theory $\mathsf{I} \Sigma_0$](./isigma0.md) |
| $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$       | `𝐈𝚺₀ + Ω₁`    | $\mathsf{I}\Sigma_0$ + $\Omega_1$-axiom |  |
| $\mathsf{EA}$              | `𝐄𝐀`     | Elementary arithmetic                             |                                                               |
| $\mathsf{I}\Sigma_1$       | `𝐈𝚺₁`    | $\mathsf{PA}^-$ + Induction of $\Sigma_1$ formula | [Theory $\mathsf{I} \Sigma_1$](./isigma1.md) |
| $\mathsf{PA}$              | `𝐏𝐀`     | Peano arithmetic                                  |                                                               |


## Defined Predicates and Functions

| Predicate/Funcrion   | Notation  | Defined in      | Totality is proved in | Complexity | Polynomial Bound | Definition |
| :-:                  | :--       | :-:             | :-:                   | :-:        | :-:   | :--
| $0$                  | `0`       | $\empty$        | $\empty$        | $\Sigma_0$ | $0$ | Included in $L_\mathsf{OR}$ |
| $1$                  | `1`       | $\empty$        | $\empty$        | $\Sigma_0$ | $1$ | Included in $L_\mathsf{OR}$ |
| $x + y$              | `x + y`   | $\empty$        | $\empty$        | $\Sigma_0$ | $x + y$ | Included in $L_\mathsf{OR}$ |
| $x \cdot y$          | `x * y`   | $\empty$        | $\empty$        | $\Sigma_0$ | $x \cdot y$ | Included in $L_\mathsf{OR}$ |
| $x = y$              | `x = y`   | $\empty$        | -               | $\Sigma_0$ | -       | Included in $L_\mathsf{OR}$ |
| $x < y$              | `x < y`   | $\empty$        | -               | $\Sigma_0$ | -       | Included in $L_\mathsf{OR}$ |
| $x \le y$            | `x ≤ y`   | $\mathsf{PA^-}$ | -               | $\Sigma_0$ | -       | [LO.Arith.instLE_logic](https://iehality.github.io/lean4-logic/docs/Logic/FirstOrder/Arith/PeanoMinus.html#LO.Arith.instLE_logic) |
| $x \mathbin{\dot{-}} y$ (modified subtraction)             | `x - y`   | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x$ | [LO.Arith.sub](https://iehality.github.io/Arithmetization/Arithmetization/Basic/PeanoMinus.html#LO.Arith.sub) |
| $x \mid y$ (devides) | `x ∣ y`   | $\mathsf{PA^-}$ | -               | $\Sigma_0$ | -       | [LO.FirstOrder.Arith.dvd](https://iehality.github.io/Arithmetization/Arithmetization/Basic/PeanoMinus.html#LO.FirstOrder.Arith.dvd) |
| $\min(x, y)$         | `min x y` | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x$     | - |
| $\max(x, y)$         | `max x y` | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x + y$ | - |
| $\lfloor x / y \rfloor$         | `x / y` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ | [LO.Arith.instDiv_arithmetization](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.instDiv_arithmetization) |
| $\mathrm{rem}(x, y)$ (remainder) | `x % y` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ | [LO.Arith.rem](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.rem) |
| $\lfloor \sqrt{x} \rfloor$ | `√x` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ | [LO.Arith.sqrt](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.sqrt) |
| $(x, y)$ | `⟪x, y⟫` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $(x + y + 1)^2$ | [LO.Arith.pair](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pair) |
| $\pi_1(x)$ (first inversion of pairing) | `π₁ x` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ | [LO.Arith.pi₁](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%81)
| $\pi_2(x)$ (second inversion of pairing) | `π₂ x` | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ | [LO.Arith.pi₂](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%82)
| $2^x$ | `exp x` | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none | [LO.Arith.Exponential](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Exp.html#LO.Arith.Exponential), [LO.Arith.instExp_arithmetization](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Exp.html#LO.Arith.instExp_arithmetization)
| $\lfloor \log_2(x) \rfloor$ | `log x` | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_0$ | $\Sigma_0$ | $x$ | [LO.Arith.log](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.log) |
| $\| x \|$ (binary length) | `‖x‖` | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_0$ | $\Sigma_0$ | $x$ | [LO.Arith.binaryLength](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.binaryLength)
| $x \# y$ | `x # y` | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ | none | [LO.Arith.instHash](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Basic.html#LO.Arith.instHash) |
| $\mathrm{Nuon}(x)$ (number of ones) | `nuon x` | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ | $x$ | [LO.Arith.nuon](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Nuon.html#LO.Arith.nuon) |
| $x \in y$, $\mathrm{Bit}(x, y)$ | `x ∈ y` | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - | [LO.Arith.Bit](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.Bit) |
| $\empty$ | `∅` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $0$ | [LO.Arith.instEmptyCollection_arithmetization](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instEmptyCollection_arithmetization)
| $x \subseteq y$ | `x ⊆ y` | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - | [LO.Arith.instHasSubset_arithmetization](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instHasSubset_arithmetization)
| $\bigcup x$ | `⋃ʰᶠ x` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none | [LO.Arith.sUnion](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sUnion)
| $x \cup y$ | `x ∪ y` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $2(x + y)$ | [LO.Arith.union](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.union)
| $\bigcap x$ | `⋂ʰᶠ x` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | ? | [LO.Arith.sInter](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sInter)
| $x \cap y$ | `x ∩ y` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ | [LO.Arith.inter](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.inter)
| $x \times y$ (cartesian product) | `x ×ʰᶠ y` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | ? | [LO.Arith.product](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.product)
| $\mathrm{domain} (x)$ (domain of relation) | `domain x` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $2 x$ | [LO.Arith.domain](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.domain)
| $\mathrm{Mapping}(x)$ | `IsMapping x` | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - | [LO.Arith.IsMapping](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.IsMapping) |
| $\mathrm{Seq}(x)$ | `Seq x` | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - | [LO.Arith.IsMapping](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.IsMapping) |
| $\mathrm{lh}(x)$ (length of sequence) | `lh x` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ | [LO.Arith.lh](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.lh)
| $x^\frown \braket{y}$ (concatation of sequence) | `x ⁀' y` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none | [LO.Arith.seqCons](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.seqCons)
| $(x)_y$ ($y$-th element of sequence) | `znth x` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ | [LO.Arith.znth](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.znth)
| $\mathrm{Semiterm}_x (y)$ | `L.Semiterm x y` | $\mathsf{I}\Sigma_1$ | - | $\Delta_1$ | - | [LO.Arith.Language.Semiterm](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Term/Basic.html#LO.Arith.Language.Semiterm) |
| $t [\vec{w}]$ | `L.termSubst n m w t` | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_1$ |  | [LO.Arith.Language.termSubst](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Term/Functions.html#LO.Arith.Language.termSubst)
| $\mathrm{Semiformula}_x(y)$ | `L.Semiformula x y` | $\mathsf{I}\Sigma_1$ | - | $\Delta_1$ | - | [LO.Arith.Language.Semiformula](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Formula/Basic.html#LO.Arith.Language.Semiformula)