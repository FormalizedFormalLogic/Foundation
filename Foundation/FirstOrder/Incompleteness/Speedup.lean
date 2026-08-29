module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1

/-!
# Minimal proof code

As a first step towards formalizing the Ehrenfeucht–Mycielski speedup theorem (1971), this
file defines `Theory.minProof T σ`, the least code of a `T`-proof of `σ`, returning `0` when
`σ` is not provable in `T`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

variable (T)

noncomputable def _root_.LO.FirstOrder.Theory.minProof (σ : Sentence L) : ℕ :=
  sInf {d : ℕ | Proof T d (⌜σ⌝ : ℕ)}

variable {T}

omit [L.DecidableEq] in
lemma proof_minProof {σ} (h : T ⊢ σ) : Proof T (T.minProof σ) (⌜σ⌝ : ℕ) :=
  Nat.sInf_mem (internalize_provability (V := ℕ) h)

lemma minProof_eq_zero_of_unprovable {σ} (h : T ⊬ σ) : T.minProof σ = 0 :=
  Nat.sInf_eq_zero.mpr <| .inr <| Set.eq_empty_iff_forall_notMem.mpr fun d hd ↦
    h (Provable.sound (⟨d, hd⟩ : Provable T (⌜σ⌝ : ℕ)))

omit [L.DecidableEq] in
lemma minProof_le {σ d} (h : Proof T d (⌜σ⌝ : ℕ)) : T.minProof σ ≤ d :=
  Nat.sInf_le h

end LO.FirstOrder.Arithmetic.Bootstrapping
