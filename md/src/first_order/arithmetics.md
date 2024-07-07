# Arithmetics

In this formalization, we prefer developping arithmetic *model theoretic*, i.e. 
show $T \models \sigma$ instead of $T \vdash \sigma$ (They are equivalent thanks to the completeness theorem.). This approach has several advantages:

1. In general, writing a formalized proof (in formalized system!) is very tedious. Meta-proofs, on the other hand, tend to be relatively concise.
2. Many definitions and proofs of logic and algebra in Mathlib can be used.
3. Metaprogramming can streamline the proof process (especially `definability`).
4. It is easy to extend predicates and functions.  When adding predicates or functions, it is necessary to extend its language by *extension by definition* in case of formalized proof, but not in model theoretic approarch.

This procedure is done as follows. 
Suppose we wish to prove that the totality of an exponential function can be proved in $\mathsf{I}\Sigma_1$.
First, the graph of the exponential function must be defined. This is achieved by the following two definitions.
1. Semantic definition.
    ```lean
    def Exponential {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₀] :
        M → M → Prop
    ```
2. Syntactic definition that expresses the semantic definition.
    ```lean
    def exponentialDef : 𝚺₀-Semisentence 2
    
    lemma Exponential.defined :
        𝚺₀-Relation (Exponential : M → M → Prop) via exponentialDef
    ```
Then prove the totality.

```lean
theorem Exponential.total  {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₀] (x : M) : ∃ y, Exponential x y
```


Since `Exponential` and `Exponential.total` are defined in all the model of $\mathsf{I}\Sigma_1$, 
`𝐈𝚺₁ ⊢! ∀' ∃' exponentialDef` is obtained by the completeness theorem. This was the result we wanted to achieve.




## Defined Predicates and Functions

| Predicate/Funcrion   | Notation  | Defined in      | Totality is proved in | Complexity | Polynomial Bound | 
| :-:                  | :--       | :-:             | :-:                   | :-:        | :-:   |
| $0$                  | `0`       | $\empty$        | $\empty$        | $\Sigma_0$ | $0$ |
| $1$                  | `1`       | $\empty$        | $\empty$        | $\Sigma_0$ | $1$ |
| $x + y$              | `x + y`   | $\empty$        | $\empty$        | $\Sigma_0$ | $x + y$ |
| $x \cdot y$          | `x * y`   | $\empty$        | $\empty$        | $\Sigma_0$ | $x \cdot y$ |
| $x = y$              | `x = y`   | $\empty$        | -               | $\Sigma_0$ | -       |
| $x < y$              | `x < y`   | $\empty$        | -               | $\Sigma_0$ | -       |
| $x \le y$            | [`x ≤ y`]((https://iehality.github.io/lean4-logic/docs/Logic/FirstOrder/Arith/PeanoMinus.html#LO.Arith.instLE_logic))   | $\mathsf{PA^-}$ | -               | $\Sigma_0$ | -       |
| $x \mathbin{\dot{-}} y$ (modified subtraction)             | [`x - y`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/PeanoMinus.html#LO.Arith.sub)   | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x$ |
| $x \mid y$ (devides) | [`x ∣ y`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/PeanoMinus.html#LO.FirstOrder.Arith.dvd)   | $\mathsf{PA^-}$ | -               | $\Sigma_0$ | -       |
| $\min(x, y)$         | `min x y` | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x$     |
| $\max(x, y)$         | `max x y` | $\mathsf{PA^-}$ | $\mathsf{PA^-}$ | $\Sigma_0$ | $x + y$ |
| $\lfloor x / y \rfloor$         | [`x / y`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.instDiv_arithmetization) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ |
| $\mathrm{rem}(x, y)$ (remainder) | [`x % y`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.rem) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ |
| $\lfloor \sqrt{x} \rfloor$ | [`√x`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.sqrt) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ |
| $(x, y)$ | [`⟪x, y⟫`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pair) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $(x + y + 1)^2$ |
| $\pi_1(x)$ (first inversion of pairing) | [`π₁ x`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%81) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ |
| $\pi_2(x)$ (second inversion of pairing) | [`π₂ x`](https://iehality.github.io/Arithmetization/Arithmetization/Basic/IOpen.html#LO.Arith.pi%E2%82%82) | $\mathsf{I_{open}}$ | $\mathsf{I_{open}}$ | $\Sigma_0$ | $x$ |
| $2^x$ | [`exp x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Exp.html#LO.Arith.Exponential) | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none |
| $\lfloor \log_2(x) \rfloor$ | [`log x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.log) | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_0$ | $\Sigma_0$ | $x$ |
| $\| x \|$ (binary length) | [`‖x‖`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaZero/Exponential/Log.html#LO.Arith.binaryLength) | $\mathsf{I}\Sigma_0$ | $\mathsf{I}\Sigma_0$ | $\Sigma_0$ | $x$ |
| $x \# y$ | [`x # y`](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Basic.html#LO.Arith.instHash) | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ | none |
| $\mathrm{Nuon}(x)$ (number of ones) | [`nuon x`](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Nuon.html#LO.Arith.nuon) | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\mathsf{I}\Sigma_0 + \mathsf{\Omega_1}$ | $\Sigma_0$ | $x$ |
| $x \in y$, $\mathrm{Bit}(x, y)$ | [`x ∈ y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.Bit) | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - |
| $\empty$ | [`∅`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instEmptyCollection_arithmetization) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $0$ |
| $x \subseteq y$ | [`x ⊆ y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Bit.html#LO.Arith.instHasSubset_arithmetization) | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - |
| $\bigcup x$ | [`⋃ʰᶠ x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sUnion) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none |
| $x \cup y$ | [`x ∪ y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.union) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $2(x + y)$ |
| $\bigcap x$ | [`⋂ʰᶠ x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.sInter) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | ? |
| $x \cap y$ | [`x ∩ y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.inter) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ |
| $x \times y$ (cartesian product) | [`x ×ʰᶠ y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.product) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | ? |
| $\mathrm{domain} (x)$ (domain of relation) | [`domain x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.domain) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $2 x$ |
| $\mathrm{Mapping}(x)$ | [`IsMapping x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Basic.html#LO.Arith.IsMapping) | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - |
| $\mathrm{Seq}(x)$ | [`Seq x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.Seq) | $\mathsf{I}\Sigma_1$ | - | $\Sigma_0$ | - |
| $\mathrm{lh}(x)$ (length of sequence) | [`lh x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.lh) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ |
| $x^\frown \braket{y}$ (concatation of sequence) | [`x ⁀' y`]((https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.seqCons)) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | none |
| $(x)_y$ ($y$-th element of sequence) | [`znth x`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/HFS/Seq.html#LO.Arith.znth) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_0$ | $x$ |
| $\mathrm{Semiterm}_x (y)$ | [`L.Semiterm x y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Term/Basic.html#LO.Arith.Language.Semiterm) | $\mathsf{I}\Sigma_1$ | - | $\Delta_1$ | - |
| $t [\vec{w}]$ | [`L.termSubst n m w t`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Term/Functions.html#LO.Arith.Language.termSubst) | $\mathsf{I}\Sigma_1$ | $\mathsf{I}\Sigma_1$ | $\Sigma_1$ | none |
| $\mathrm{Semiformula}_x(y)$ | [`L.Semiformula x y`](https://iehality.github.io/Arithmetization/Arithmetization/ISigmaOne/Metamath/Formula/Basic.html#LO.Arith.Language.Semiformula) | $\mathsf{I}\Sigma_1$ | - | $\Delta_1$ | - |
