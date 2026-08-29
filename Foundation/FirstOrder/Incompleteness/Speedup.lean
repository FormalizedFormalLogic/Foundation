module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce
public import Mathlib.Data.Nat.Log

/-!
# Ehrenfeucht–Mycielski speedup theorem

`Theory.minProof T σ` is the least code of a `T`-proof of `σ`, and `0` when `σ` is not
`T`-provable.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

section
variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or :
    insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨λ h ↦ by cl_prover [h], λ h ↦ by cl_prover [h]⟩

end

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

variable (T)

noncomputable def _root_.LO.FirstOrder.Theory.minProof (σ : Sentence L) : ℕ :=
  sInf {d : ℕ | Proof T d (⌜σ⌝ : ℕ)}

variable {T} {σ : Sentence L}

lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) (⌜σ⌝ : ℕ) :=
  Nat.sInf_mem (internalize_provability (V := ℕ) h)

lemma minProof_eq_zero_of_unprovable [L.DecidableEq] (h : T ⊬ σ) : T.minProof σ = 0 :=
  Nat.sInf_eq_zero.mpr <| .inr <| Set.eq_empty_iff_forall_notMem.mpr λ d hd ↦
    h (Provable.sound (⟨d, hd⟩ : Provable T (⌜σ⌝ : ℕ)))

lemma minProof_le {d} (h : Proof T d (⌜σ⌝ : ℕ)) : T.minProof σ ≤ d :=
  Nat.sInf_le h

section Speedup

open Encodable

lemma computablePred_proof (T : Theory L) [T.Δ₁] :
    ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  obtain ⟨φ, hφ⟩ := HierarchySymbol.Definable.of_delta (Γ := 𝚺) (Proof.definable (V := ℕ) (T := T))
  obtain ⟨ψ, hψ⟩ := (HierarchySymbol.Definable.of_delta (Γ := 𝚷) (Proof.definable (V := ℕ) (T := T))).notPi
  have hcomp : Computable λ p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.to_comp <|
      Primrec.vector_cons.comp .fst (Primrec.vector_cons.comp .snd (.const List.Vector.nil))
  exact ⟨((sigma1_re id φ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hφ.iff (v := ![p.1, p.2]),
    ((sigma1_re id ψ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hψ.iff (v := ![p.1, p.2])⟩

lemma computable_minProof_comp (T : Theory L) [T.Δ₁] [L.Primcodable] {α : Type*} [Primcodable α]
    {F : α → Sentence L} (hF : Computable F) (hprov : ∀ a, T ⊢ F a) :
    Computable λ a ↦ T.minProof (F a) := by
  classical
  have hex : ∀ a, ∃ d, Proof T d (⌜F a⌝ : ℕ) :=
    λ a ↦ ⟨T.minProof (F a), proof_minProof (hprov a)⟩
  have hcomp : ComputablePred λ p : α × ℕ ↦ Proof T p.2 (⌜F p.1⌝ : ℕ) := by
    obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (computablePred_proof T)
    refine ComputablePred.computable_iff.mpr
      ⟨λ p ↦ f (p.2, encode (F p.1)),
        hf.comp (Computable.pair Computable.snd (Computable.encode.comp (hF.comp Computable.fst))),
        funext λ p ↦ ?_⟩
    simp only [Sentence.quote_eq_encode_nat]
    exact congrFun hfe (p.2, encode (F p.1))
  exact (Computable.find hcomp hex).of_eq λ a ↦ (Nat.sInf_def (hex a)).symm

lemma computable_insert_minProof_or [L.DecidableEq] [L.Primcodable] :
    Computable λ π : Sentence L ↦ (insert σ T).minProof (σ ⋎ π) :=
  computable_minProof_comp (insert σ T)
    (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp
    λ π ↦ Entailment.deduction_iff.mpr (by cl_prover)

lemma computablePred_bddExists_proof (T : Theory L) [T.Δ₁] {α : Type*} [Primcodable α]
    (bd cd : α → ℕ) (hbd : Computable bd) (hcd : Computable cd) :
    ComputablePred λ a : α ↦ ∃ d ≤ bd a, Proof T d (cd a) := by
  obtain ⟨χ, hχ, hχe⟩ := ComputablePred.computable_iff.mp (computablePred_proof T)
  have hstep : Computable (λ q : α × (ℕ × Bool) ↦ Bool.or q.2.2 (χ (q.2.1, cd q.1))) :=
    Computable₂.comp Primrec.or.to_comp (Computable.snd.comp Computable.snd)
      (hχ.comp (Computable.pair (Computable.fst.comp Computable.snd) (hcd.comp Computable.fst)))
  have hS : Computable λ a : α ↦
      Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, cd a)) (bd a + 1) :=
    Computable.nat_rec (Computable.succ.comp hbd) (Computable.const false) hstep.to₂
  have key : ∀ N e, (Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, e)) (N + 1) = true) ↔
      ∃ d ≤ N, χ (d, e) = true := by
    intro N e
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Bool.or_eq_true_iff, ih]
        grind
  refine ComputablePred.computable_iff.mpr ⟨_, hS, funext λ a ↦ propext ?_⟩
  rw [key (bd a) (cd a)]
  exact exists_congr λ d ↦ and_congr_right λ _ ↦ (congrFun hχe (d, cd a)).to_iff

/-- The Ehrenfeucht–Mycielski speedup theorem [EM71]. -/
theorem ehrenfeucht_mycielski_speedup [L.DecidableEq] [L.Primcodable]
    (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π := by
  by_contra h
  push Not at h
  apply hU
  refine ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm)
  refine ComputablePred.of_eq
    (computablePred_bddExists_proof T (λ π ↦ f ((insert σ T).minProof (σ ⋎ π)))
      (λ π ↦ encode (σ ⋎ π)) (hf.comp computable_insert_minProof_or)
      (Computable.encode.comp (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp))
    λ π ↦ ?_
  constructor
  · rintro ⟨d, _, hd⟩
    exact Provable.sound (⟨d, by rwa [Sentence.quote_eq_encode_nat]⟩ : Provable T (⌜σ ⋎ π⌝ : ℕ))
  · intro hp
    exact ⟨T.minProof (σ ⋎ π), h (σ ⋎ π) hp, by
      have := proof_minProof hp
      rwa [Sentence.quote_eq_encode_nat] at this⟩

theorem ehrenfeucht_mycielski_speedup_arithmetic (T : ArithmeticTheory) [T.Δ₁] (σ : ArithmeticSentence)
    [𝗜𝚺₁ ⪯ T] (hσ : T ⊬ σ) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗜𝚺₁ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗜𝚺₁ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T))
  have : Entailment.Consistent (insert (∼σ) T) := Entailment.unprovable_iff_consistent_adjoin.mp hσ
  ehrenfeucht_mycielski_speedup
    (uncomputable_theory_of_consistent : ¬ComputablePred (insert (∼σ) T).theory) f hf

example {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗜𝚺₁ ⪯ T] (hσ : T ⊬ σ) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π) := by
  obtain ⟨π, hπ, hlt⟩ := ehrenfeucht_mycielski_speedup_arithmetic T σ hσ (λ x ↦ 2 ^ (x + 1))
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ).to_comp)
  exact ⟨π, hπ, (Nat.le_log_iff_pow_le (b := 2) (by norm_num)
    (((Nat.zero_le _).trans_lt hlt).ne')).mpr hlt.le⟩

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
