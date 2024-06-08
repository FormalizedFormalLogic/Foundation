# Gödel's First Incompleteness Theorem

Summarize Gödel's First Incompleteness Theorem.

## Definition

If system $\mathcal{S}$ can prove or refute for every formula $\varphi$ of $\mathcal{S}$, $\mathcal{S}$ is called _complete_.
Otherwise, $\mathcal{S}$ is called _incomplete_.

```lean
def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ~f
```

If some formula $\varphi$ exists and $\varphi$ is not provable nor refutable in `\mathcal{S}`, $\mathcal{S}$ is called _undecidable_.
Obviously $\mathcal{S}$ is incomplete iff undecidable.

```lean
def Undecidable (f : F) : Prop := 𝓢 ⊬! f ∧ 𝓢 ⊬! ~f

lemma incomplete_iff_exists_undecidable : ¬System.Complete 𝓢 ↔ ∃ f, Undecidable 𝓢 f
```

## Theorem

Let $T$ is $𝐏𝐀⁻$-extension, $\Sigma_1$-sound, and computable first-order theory. Then, $T$ is incomplete.

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
- [Gödel's first incompleteness theorem](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.first_incompleteness)


## About Second Theorem

To demonstrate the second incompleteness theorem, as outlined in Gödel's original paper, one can derive it by proving the first incompleteness theorem again within arithmetic.
Although this fact has not yet been formalized in this project.
These efforts are being undertaken in a separated repository [iehality/Arithmetization](https://github.com/iehality/Arithmetization) from this project.

Notably, the formalization of the second incompleteness theorem has already been accomplished by L. C. Paulson in Isabelle.
However, owing to the technical simplicity for coding and others. this formalization is on *hereditarily finite sets* and not on arithmetic.
- [L. C. Paulson, "A machine-assisted proof of Gödel's incompleteness theorems for the theory of hereditarily finite sets"](https://www.repository.cam.ac.uk/items/bda52431-26e0-4e86-8d63-409bcedd4617)
- [Isabelle AFP](https://www.isa-afp.org/entries/Incompleteness.html)
