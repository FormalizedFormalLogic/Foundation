# Strength between Logics

It is immediately apparent that, when `𝓓₁​` and `𝓓₂` are same inference rule[^strength_between_modal_logics_1], the logical strength between `𝓓₁` and `𝓓₂` is determined by the subset of their axiom set.

```lean
lemma reducible_of_subset (hNec : L₁.nec ≤ L₂.nec) (hAx : Ax(L₁) ⊆ Ax(L₂)) : L₁ ≤ₛ L₂ := by

lemma reducible_K_KT : 𝐊 ≤ₛ 𝐊𝐓
```
- [LO.Modal.Standard.Deduction.reducible_of_subset](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Deduction.html#LO.Modal.Standard.Deduction.reducible_of_subset)
- [LO.Modal.Standard.reducible_K_KT](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Deduction.html#LO.Modal.Standard.reducible_K_KT)

However, even without the subset of axiomset, it is possible to analyze the strength of logic via Kripke semantics, specifically by analyzing the properties of frames defined by the axioms. For example, since seriality follows from reflexivity, $\bf KT$ is stronger than $\bf KD$ ($\sf K \cup D \not\sube K \cup T$).

```lean
lemma reducible_of_definability
  [Sound 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Complete 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Definability Ax(𝓓₁​) P₁] [Definability Ax(𝓓₂) P₂]
  (hs : ∀ {F : Frame}, P₂ F → P₁ F)
  : 𝓓₁​ ≤ₛ 𝓓₂

theorem reducible_KD_KT : 𝐊𝐃 ≤ₛ 𝐊𝐓
```
- [LO.Modal.Standard.Kripke.reducible_of_definability](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/Reducible.html#LO.Modal.Standard.Kripke.reducible_of_definability)
- [LO.Modal.Standard.reducible_KD_KT](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/Geach/Reducible.html#LO.Modal.Standard.reducible_KD_KT)

By same argument, the equivalence of provability between logics can be analyzed. $\bf S5$ is equivalent to $\bf KT4B$ ($\sf K \cup T \cup 5 \neq K \cup T \cup 4 \cup B$).

```lean
lemma equiv_of_iff_definability
  [Sound 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Sound 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Complete 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Complete 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Definability Ax(𝓓₁​) P₁] [Definability Ax(𝓓₂) P₂]
  (h : ∀ {F : Frame}, P₁ F ↔ P₂ F) : 𝓓₁​ =ₛ 𝓓₂

theorem equiv_S5_KT4B : 𝐒𝟓 =ₛ 𝐊𝐓𝟒𝐁
```
- [LO.Modal.Standard.Kripke.equiv_of_iff_definability](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/Reducible.html#LO.Modal.Standard.Kripke.equiv_of_iff_definability)
- [LO.Modal.Standard.equiv_S5_KT4B](https://iehality.github.io/lean4-logic/docs/Logic/Modal/Standard/Kripke/Geach/Reducible.html#LO.Modal.Standard.equiv_S5_KT4B)

[^strength_between_modal_logics_1]: It is permissible that `𝓓₂` has all inference rule of `𝓓₁​`.
