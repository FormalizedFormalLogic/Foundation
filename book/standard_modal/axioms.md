# Axioms

As an example, describe about axiom $\sf K$. Other axioms such as $\sf T$ and $\sf 4$ follow the same manner.

```lean
-- Axiom schema
abbrev System.Axioms.K (p q : F) := □(p ⟶ q) ⟶ □p ⟶ □q

abbrev Modal.Standard.AxiomSet (α : Type*) := Set (Modal.Standard.Formula α)

abbrev Modal.Standard.AxiomSet.K : AxiomSet α := { System.Axioms.K p q | (p) (q) }

notation "𝗞" => Modal.Standard.AxiomSet.K
```

## Well-Known Axioms

| Notation | Name | Schema | Geach |
| :-: | :-: | :-: | :-: |
| `𝗞` | K   | `□(p ⟶ q) ⟶ □p ⟶ □q` | |
| `𝗧` | T    | `□p ⟶ p`     | ✅ |
| `𝗕` | B    | `p ⟶ □◇p`   | ✅ |
| `𝗗` | D    | `□p ⟶ ◇p`   | ✅ |
| `𝟰` | Four | `□p ⟶ □□p`  | ✅ |
| `𝟱` | Five | `◇p ⟶ □◇p`  | ✅ |
| `.𝟮` | Dot2 | `◇□p ⟶ □◇p` | ✅ |
| `.𝟯` | Dot3 | `□(□p ⟶ □q) ⋎ □(□q ⟶ □p)` |
| `𝗟` | L    | `□(□p ⟶ p) ⟶ □p` |
| `𝗚𝗿𝘇` | Grz  | `□(□(p ⟶ □p) ⟶ p) ⟶ p` |
| `𝗧𝗰` | Tc   | `p ⟶ □p`    | ✅ |
| `𝗩𝗲𝗿` | Ver  | `□p`         |
| `𝗖𝟰` | C4   | `□□p ⟶ □p`  | ✅ |
| `𝗖𝗗` | CD   | `◇p ⟶ □p`   | ✅ |
| `𝗠` | M    | `□◇p ⟶ ◇□p` | |

## Geach Axioms

Geach Axiom is defined as $\mathsf{ga}_{i,j,m,n} \equiv \Diamond^i \Box^m p \to \Box^j \Diamond^n p$.

```lean
structure Geach.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

abbrev Geach (l : Geach.Taple) (p : F) := ◇^[l.i](□^[l.m]p) ⟶ □^[l.j](◇^[l.n]p)
notation "𝗴𝗲(" t ")" => AxiomSet.Geach t
```

Some axioms is generalized as Geach axioms (Above table, Geach: ✅).
For example $\mathsf{T} \equiv \mathsf{ga}_{0,0,1,0}$ and $\mathsf{4} \equiv \mathsf{ga}_{0,2,1,0}$.

