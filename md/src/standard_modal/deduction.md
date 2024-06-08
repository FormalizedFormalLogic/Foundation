# Deduction System for Modal Logic

Our Hilbert-style deduction system for modal logic is designed to take parameters.
These parameters are as follows.

```lean
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
  nec : Bool
```

- `axiomSet` is set of formula (aximos), For example, `𝗞`, `𝗞 ∪ 𝗧 ∪ 𝟰`.
- `nec` is flag to contain necessitation rule.

The parameter is called _Normal_ if `axiomSet` includes `𝗞` and `nec` is `true`.

In this formalization, **modal logics** that we usually refer to as $\bf K$, $\bf S4$, etc. is characterized by deduction parameter.

## Geach Logic

```lean
def AxiomSet.MultiGeach : List Axioms.Geach.Taple → AxiomSet α
  | [] => 𝗞
  | x :: xs => (AxiomSet.Geach x) ∪ (AxiomSet.MultiGeach xs)
notation "𝗚𝗲(" l ")" => AxiomSet.MultiGeach l

def DeductionParameter.Geach (l : List Axioms.Geach.Taple) : DeductionParameter α where
  axiomSet := 𝗚𝗲(l)
  nec := true
notation "𝐆𝐞(" l ")" => DeductionParameter.Geach l
```

If `𝓓` is some `𝐆𝐞(l)`, `𝓓` is called *Geach*.

```
class IsGeach (𝓓 : DeductionParameter α) where
  taples : List Axioms.Geach.Taple
  char : 𝓓 = 𝐆𝐞(taples)
```
