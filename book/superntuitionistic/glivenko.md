# Glivenko's Theorem

If $\varphi$ is provable in classical logic, double negation inserted $\lnot\lnot\varphi$ is provable in intuitionistic logic.

```lean
theorem iff_provable_dn_efq_dne_provable: 𝐈𝐧𝐭 ⊢! ~~p ↔ 𝐂𝐥 ⊢! p
```
