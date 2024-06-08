# Soundness for Kripke Semantics

Let deduction system of `𝓓` has necessitation. If `𝓓 ⊢! p` then `p` is valid on every frame in `𝔽(Ax(𝓓))`.

```lean
instance [HasNec 𝓓] : Sound 𝓓 𝔽(Ax(𝓓))
```

#### Consistency of Deduction System via Kripke Semantics

From soundness theorem, if `𝔽(Ax(𝓓))` is nonempty, deduction system of `𝓓` is consistent (i.e. not every formula is provable in `𝓓`).

```lean
instance [FrameClass.IsNonempty 𝔽(Ax(𝓓))] : System.Consistent 𝓓
```

It is immediately apparent, frameclass of `𝔽(Ax(𝐊))` is nonempty, thus `𝐊` is consistent.

```lean
instance : FrameClass.IsNonempty 𝔽(Ax(𝐊))

instance : System.Consistent 𝐊
```
- [`LO.System.Consistent 𝐊`](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/Soundness.html#LO.Modal.Standard.Kripke.instConsistentFormulaDeductionParameterInstSystemFormulaDeductionParameterK)

Futhermore, if `𝓓` is Geach, then its frameclass is nonempty, thus it is consistent.

```lean
instance [𝓓.IsGeach] : FrameClass.IsNonempty 𝔽(Ax(𝓓))

instance [𝓓.IsGeach] : System.Consistent 𝓓
```
