# On Gödel-Löb Logic

## Logics Equivalent to GL

Introduct Henkin Axiom `𝗛`, Löb Rule `(𝐋)`, Henkin Rule `(𝐇)`.

```lean
protected abbrev H := □(□p ⟷ p) ⟶ □p

class LoebRule where
  loeb {p : F} : 𝓢 ⊢ □p ⟶ p → 𝓢 ⊢ p

class HenkinRule where
  henkin {p : F} : 𝓢 ⊢ □p ⟷ p → 𝓢 ⊢ p
```

- `𝐊𝟒𝐇` is defined normal logic that axioms are `𝗞`, `𝟰`, `𝗛`.
- `𝐊𝟒(𝐋)` is defined as `𝐊𝟒` extended `(𝐋)`.
- `𝐊𝟒(𝐇)` is defined as `𝐊𝟒` extended `(𝐇)`.

These logics are equivalent to `𝐆𝐋`.

```lean
lemma reducible_GL_K4Loeb : 𝐆𝐋 ≤ₛ 𝐊𝟒(𝐋)
lemma reducible_K4Loeb_K4Henkin: 𝐊𝟒(𝐋) ≤ₛ 𝐊𝟒(𝐇)
lemma reducible_K4Henkin_K4H : 𝐊𝟒(𝐇) ≤ₛ 𝐊𝟒𝐇
lemma reducible_K4Henkin_GL : 𝐊𝟒𝐇 ≤ₛ 𝐆𝐋

--- Obviously `𝐆𝐋 =ₛ 𝐊𝟒(𝐋) =ₛ 𝐊𝟒(𝐇) =ₛ 𝐊𝟒𝐇`, since transivity of `≤ₛ` and definition of `=ₛ`.
```

Note: `𝐊𝐇` (normal logic that axioms are `𝗞`, `𝗛`) is proper weak logic of `𝐆𝐋` and not Kripke complete.
