# Rejection Law of Excluded Middle

Law of Excluded Middle (LEM) is not always provable in intuitionistic logic.

```lean
theorem noLEM : ∃ (p : Formula α), 𝐈𝐧𝐭 ⊬! p ⋎ ~p := by
```

Thus, intuitionistic logic is proper weaker than classical logic, since LEM is always provable in classical logic.

```lean
theorem strictReducible_intuitionistic_classical : 𝐈𝐧𝐭 <ₛ 𝐂𝐥
```
