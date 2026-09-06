module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Primrec
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce
public import Mathlib.Data.Nat.Log

/-!
# Ehrenfeucht–Mycielski speedup theorem

`Theory.minProof T σ` is the least Gödel code of a proof `T ⊢!₂! ↑σ`, and `0` when `σ` is not
`T`-provable.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

section Provability

variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or : ∼σ ⫽ T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨λ h ↦ by cl_prover [h], λ h ↦ by cl_prover [h]⟩

end Provability

variable
  {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
  {T : Theory L} [T.Δ₁] {σ : Sentence L}

noncomputable def _root_.LO.FirstOrder.Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ :=
  sInf (Set.range λ d : T ⊢!₂! (σ : Proposition L) ↦ (⌜d⌝ : ℕ))

@[grind →]
lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) ⌜σ⌝ := by
  obtain ⟨d, hd⟩ : T.minProof σ ∈ Set.range (λ d : T ⊢!₂! (σ : Proposition L) ↦ (⌜d⌝ : ℕ)) :=
    Nat.sInf_mem ⟨_, Set.mem_range_self (provable_iff_derivable2.mp h).some⟩
  exact hd ▸ proof_of_quote_proof2 d

@[grind →]
lemma minProof_eq_zero_of_unprovable (h : T ⊬ σ) : T.minProof σ = 0 := by
  have : IsEmpty (T ⊢!₂! (σ : Proposition L)) :=
    not_nonempty_iff.mp λ hd ↦ h (provable_iff_derivable2.mpr hd)
  simp [Theory.minProof, Set.range_eq_empty_iff.mpr this]

@[grind ←]
lemma minProof_le (d : T ⊢!₂! (σ : Proposition L)) : T.minProof σ ≤ ⌜d⌝ :=
  Nat.sInf_le (Set.mem_range_self d)

open Encodable

variable {α : Type*} [Primcodable α] {F : α → Sentence L}

omit [L.DecidableEq] in
lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 :=
  have h : ComputablePred λ n : ℕ ↦ Proof T (π₁ n) (π₂ n) :=
    computablePred_iff_delta1.mpr (by definability)
  ComputablePred.computable_of_manyOneReducible
    ⟨λ p ↦ Nat.pair p.1 p.2, Primrec₂.natPair.to_comp, λ p ↦ by simp [← nat_pair_eq]⟩ h

omit [L.DecidableEq] in
private lemma definable_bddExists_proof :
    𝚫₁-Predicate λ n : ℕ ↦ ∃ d ≤ π₁ n, Proof T d (π₂ n) :=
  (HierarchySymbol.Definable.bexs_ble (ℌ := 𝚫₁) (f := λ v : Fin 1 → ℕ ↦ π₁ (v 0))
    (P := λ v x ↦ Proof T x (π₂ (v 0))) (by simp) (by definability)).of_iff <| λ v ↦
      exists_congr λ d ↦ and_congr_left' (by simp only [Arithmetic.le_def]; omega)

omit [L.DecidableEq] in
lemma computablePred_bddExists_proof [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
    (hbd : Computable bd) :
    ComputablePred λ a ↦ ∃ d ≤ bd a, Proof T d ⌜F a⌝ :=
  ComputablePred.computable_of_manyOneReducible
    ⟨λ a ↦ Nat.pair (bd a) (encode (F a)),
      Computable₂.comp Primrec₂.natPair.to_comp hbd (Computable.encode.comp hF),
      λ a ↦ by simp [← nat_pair_eq, Sentence.quote_eq_encode_nat]⟩
    (computablePred_iff_delta1.mpr (definable_bddExists_proof (T := T)))

lemma computablePred_provable_of_minProof_le [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
    (hbd : Computable bd) (hb : ∀ a, T ⊢ F a → T.minProof (F a) ≤ bd a) :
    ComputablePred λ a ↦ T ⊢ F a := by
  apply ComputablePred.of_eq (computablePred_bddExists_proof (T := T) hF hbd);
  intro a;
  have hp : ∀ d, Proof T d ⌜F a⌝ → T ⊢ F a := λ d hd ↦ provable_iff_provable.mp ⟨d, hd⟩;
  grind;

private def speedupProof (T : Theory L) (σ π : Sentence L) : σ ⫽ T ⊢!₂! ((σ ⋎ π : Sentence L)) :=
  Derivation2.or (φ := σ) (ψ := π) (by simp) $
    Derivation2.axm σ (by simp) (by simp)

private lemma computable_quote_speedupProof [L.Primcodable] :
    Computable λ π ↦ (⌜speedupProof T σ π⌝ : ℕ) :=
  have hπ : Primrec λ π : Sentence L ↦ (⌜(π : Proposition L)⌝ : ℕ) :=
    Primrec.encode.of_eq λ π ↦ (Sentence.quote_eq_encode_nat π).symm;
  have hσπ : Primrec λ π : Sentence L ↦ (⌜((σ ⋎ π : Sentence L) : Proposition L)⌝ : ℕ) :=
    (Primrec.encode.comp (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id)).of_eq
      λ π ↦ (Sentence.quote_eq_encode_nat (σ ⋎ π)).symm;
  Primrec.to_comp <|
    primrec_quote_or (primrec_quote_singleton hσπ) (.const _) hπ
      (primrec_quote_axm
        (primrec_quote_insert (.const _) (primrec_quote_insert hπ (primrec_quote_singleton hσπ)))
        (.const _))

private lemma minProof_or_le_speedupProof (π : Sentence L) :
    (σ ⫽ T).minProof (σ ⋎ π) ≤ ⌜speedupProof T σ π⌝ := minProof_le (speedupProof T σ π)

/-- The Ehrenfeucht–Mycielski speedup theorem.

- [EM71] -/
theorem ehrenfeucht_mycielski_speedup [L.Primcodable]
    (hU : ¬ComputablePred (∼σ ⫽ T).theory) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((σ ⫽ T).minProof π) < T.minProof π := by
  contrapose! hU;
  refine ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm);
  exact computablePred_provable_of_minProof_le
    (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp
    ((Nat.computable_boundedMax hf).comp computable_quote_speedupProof)
    λ π hπ ↦ (hU (σ ⋎ π) hπ).trans (Nat.le_boundedMax (minProof_or_le_speedupProof π));

section Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

open LO.Entailment in
theorem ehrenfeucht_mycielski_speedup_arithmetic (hσ : T ⊬ σ) (f : ℕ → ℕ) (hf : Computable f) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((σ ⫽ T).minProof π) < T.minProof π :=
  have : 𝗜𝚺₁ ⪯ (∼σ ⫽ T) := WeakerThan.trans ‹𝗜𝚺₁ ⪯ T› (Axiomatized.le_of_subset (Set.subset_insert _ T));
  have : Consistent (∼σ ⫽ T) := unprovable_iff_consistent_adjoin.mp hσ;
  ehrenfeucht_mycielski_speedup (uncomputable_theory_of_consistent : ¬ComputablePred (∼σ ⫽ T).theory) f hf

example (hσ : T ⊬ σ) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ (σ ⫽ T).minProof π < Nat.log 2 (T.minProof π) := by
  obtain ⟨π, hπ, hlt⟩ := ehrenfeucht_mycielski_speedup_arithmetic hσ (λ x ↦ 2 ^ (x + 1)) $
    Primrec₂.unpaired'.1 Nat.Primrec.pow
      |>.comp (Primrec.const 2) Primrec.succ
      |>.to_comp;
  use π;
  and_intros;
  . exact hπ;
  . apply Nat.le_log_iff_pow_le (by grind) (by grind) |>.mpr;
    omega;

end Arithmetic

end LO.FirstOrder.Arithmetic.Bootstrapping
