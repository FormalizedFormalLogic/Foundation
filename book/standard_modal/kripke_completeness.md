# Completeness for Kripke Semantics

Completeness for Kripke Semantics (shortly called, _Kripke Completeness_) proved by usual way with Canonical frames and models.

If every axioms in `Ax(𝓓)` is valid in Canonical frame of `𝓓`, `𝓓` is called _Canonical_.

```
class Canonical (𝓓 : DeductionParameter α) [Inhabited (MCT 𝓓)] where
  realize : (CanonicalFrame 𝓓) ⊧* Ax(𝓓)
```

If `𝓓` is canonical and consistent, then `𝓓` is complete for `𝔽(Ax(𝓓))`.

```
instance [System.Consistent 𝓓] [Canonical 𝓓] : Complete 𝓓 𝔽(Ax(𝓓))
```

Immediately apparent that `𝐊` is canonical and `𝐊` is consistent mentioned above, then `𝐊` is complete.

```
instance : Canonical 𝐊

instance : Complete 𝐊 𝔽(Ax(𝐊))
```

Futhermore, if `𝓓` is Geach, then `𝓓` is canonical, thus it is complete.

```lean
instance [𝓓.IsGeach] : Canonical 𝓓

instance [𝓓.IsGeach] : Complete 𝓓 𝔽(Ax(𝓓))
```
