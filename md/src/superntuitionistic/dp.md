# Disjunctive Property

Intuitionistic Logic have Disjunctive Property (DP).

```lean
class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

instance : Disjunctive 𝐈𝐧𝐭
```
