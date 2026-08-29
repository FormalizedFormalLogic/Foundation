module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Incompleteness.Church
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

open Encodable
variable {σ : Sentence L}

lemma provable_insert_neg_iff_or {π : Sentence L} :
    insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π := sorry

lemma computablePred_proof : ComputablePred fun p : ℕ × ℕ ↦ Proof T p.1 p.2 := sorry

lemma exists_computable_bound_minProof_imp_or :
  ∃ g : ℕ → ℕ, Computable g ∧ ∀ π : Sentence L, T.minProof (σ 🡒 (σ ⋎ π)) ≤ g (encode π) := sorry

lemma exists_computable_bound_insert_minProof :
  ∃ r : ℕ → ℕ, Computable r ∧ ∀ π : Sentence L, T ⊢ σ 🡒 π → (insert σ T).minProof π ≤ r (T.minProof (σ 🡒 π)) := sorry

lemma not_exists_computable_monotone_bound_minProof [L.Primcodable]
  (hU : ¬ComputablePred fun π : Sentence L ↦ insert (∼σ) T ⊢ π) :
  ¬∃ f : ℕ → ℕ, Computable f ∧ Monotone f ∧ ∀ π : Sentence L, T ⊢ π → T.minProof π ≤ f (T.minProof (σ 🡒 π)) := sorry

/-- The Ehrenfeucht–Mycielski speedup theorem: if the set of `T + ∼σ`-provable sentences is not
computable, then adjoining `σ` to `T` as a new axiom gives an unbounded proof-length speedup over
`T`, in the sense that no computable monotone function bounds the minimal `T`-proof code of a
`T`-provable `π` in terms of the minimal `(T + σ)`-proof code of `π`.
- [EM71, Theorem] -/
theorem ehrenfeucht_mycielski_speedup [L.Primcodable]
  (hU : ¬ComputablePred fun π : Sentence L ↦ insert (∼σ) T ⊢ π) :
  ¬∃ s : ℕ → ℕ, Computable s ∧ Monotone s ∧ ∀ π : Sentence L, T ⊢ π → T.minProof π ≤ s ((insert σ T).minProof π) := sorry

/-- The hypothesis `hU` in `ehrenfeucht_mycielski_speedup` is automatically satisfied when `T` is
an arithmetic theory extending `𝗥₀` and sound on `𝚺₁` sentences, by Church's theorem. -/
theorem ehrenfeucht_mycielski_speedup' {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ insert (∼σ) T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] :
    ¬∃ s : ℕ → ℕ, Computable s ∧ Monotone s ∧
      ∀ π : ArithmeticSentence, T ⊢ π → T.minProof π ≤ s ((insert σ T).minProof π) :=
  ehrenfeucht_mycielski_speedup (church_theorem_general (T := insert (∼σ) T))

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
