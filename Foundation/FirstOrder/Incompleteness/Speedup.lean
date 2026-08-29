module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Mathlib.Computability.Reduce

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

section Speedup

variable [L.Primcodable] {α : Sentence L}

omit [L.Primcodable] in
lemma provable_insert_neg_iff_or {σ : Sentence L} :
    insert (∼α) T ⊢ σ ↔ T ⊢ α ⋎ σ := sorry

omit [L.Primcodable] in
lemma computablePred_proof : ComputablePred fun p : ℕ × ℕ ↦ Proof T p.1 p.2 := sorry

omit [L.Primcodable] in
lemma exists_computable_bound_minProof_imp_or :
    ∃ g : ℕ → ℕ, Computable g ∧
      ∀ σ : Sentence L, T.minProof (α 🡒 (α ⋎ σ)) ≤ g (Encodable.encode σ) := sorry

omit [L.Primcodable] in
lemma exists_computable_bound_insert_minProof :
    ∃ r : ℕ → ℕ, Computable r ∧
      ∀ τ : Sentence L, T ⊢ α 🡒 τ → (insert α T).minProof τ ≤ r (T.minProof (α 🡒 τ)) := sorry

lemma not_exists_computable_monotone_bound_minProof
    (hU : ¬ComputablePred fun σ : Sentence L ↦ insert (∼α) T ⊢ σ) :
    ¬∃ f : ℕ → ℕ, Computable f ∧ Monotone f ∧
      ∀ τ : Sentence L, T ⊢ τ → T.minProof τ ≤ f (T.minProof (α 🡒 τ)) := sorry

/-- The Ehrenfeucht–Mycielski speedup theorem: if the set of `T + ∼α`-provable sentences is not
computable, then adjoining `α` to `T` as a new axiom gives an unbounded proof-length speedup over
`T`, in the sense that no computable monotone function bounds the minimal `T`-proof code of a
`T`-provable `τ` in terms of the minimal `(T + α)`-proof code of `τ`.
- [EM71, Theorem] -/
theorem ehrenfeucht_mycielski_speedup
    (hU : ¬ComputablePred fun σ : Sentence L ↦ insert (∼α) T ⊢ σ) :
    ¬∃ s : ℕ → ℕ, Computable s ∧ Monotone s ∧
      ∀ τ : Sentence L, T ⊢ τ → T.minProof τ ≤ s ((insert α T).minProof τ) := sorry

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
