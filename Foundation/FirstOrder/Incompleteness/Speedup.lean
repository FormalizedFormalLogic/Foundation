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

lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
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

lemma computable_minProof_comp [L.Primcodable] {α : Type*} [Primcodable α] {F : α → Sentence L}
    (hF : Computable F) (hprov : ∀ a, T ⊢ F a) :
    Computable λ a ↦ T.minProof (F a) := by
  classical
  have hex : ∀ a, ∃ d, Proof T d (⌜F a⌝ : ℕ) :=
    λ a ↦ ⟨T.minProof (F a), proof_minProof (hprov a)⟩
  have hcomp : ComputablePred λ p : α × ℕ ↦ Proof T p.2 (⌜F p.1⌝ : ℕ) := by
    obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T))
    refine ComputablePred.computable_iff.mpr
      ⟨λ p ↦ f (p.2, encode (F p.1)),
        hf.comp (Computable.pair Computable.snd (Computable.encode.comp (hF.comp Computable.fst))),
        funext λ p ↦ ?_⟩
    simp only [Sentence.quote_eq_encode_nat]
    exact congrFun hfe (p.2, encode (F p.1))
  exact (Computable.find hcomp hex).of_eq λ a ↦ (Nat.sInf_def (hex a)).symm

omit [L.LORDefinable] in
lemma computable_or_left [L.Primcodable] : Computable λ π : Sentence L ↦ σ ⋎ π := by
  set b : ℕ := encode σ with hb
  have hCode : Primrec λ e : ℕ ↦ (Nat.pair 5 <| b.pair e) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
      (Primrec₂.natPair.comp (Primrec.const b) Primrec.id))
  refine (Computable.ofOption ((Computable.decode (α := Sentence L)).comp
    (hCode.to_comp.comp Computable.encode))).of_eq_tot λ π ↦ ?_
  have he : (Nat.pair 5 <| b.pair (encode π)) + 1 = encode (σ ⋎ π) := by rw [hb]; rfl
  simp [he, Encodable.encodek]

lemma computable_insert_minProof_or [L.DecidableEq] [L.Primcodable] :
    Computable λ π : Sentence L ↦ (insert σ T).minProof (σ ⋎ π) :=
  computable_minProof_comp (T := insert σ T) computable_or_left
    λ π ↦ Entailment.deduction_iff.mpr (by cl_prover)

lemma computablePred_bddExists_proof {α : Type*} [Primcodable α] {bd cd : α → ℕ}
    (hbd : Computable bd) (hcd : Computable cd) :
    ComputablePred λ a : α ↦ ∃ d ≤ bd a, Proof T d (cd a) := by
  obtain ⟨χ, hχ, hχe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T))
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
        show ((Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, e)) (n + 1)) ||
            χ (n + 1, e)) = true ↔ ∃ d ≤ n + 1, χ (d, e) = true
        rw [Bool.or_eq_true_iff, ih]
        constructor
        · rintro (⟨d, hd, hc⟩ | h)
          · exact ⟨d, hd.trans (Nat.le_succ n), hc⟩
          · exact ⟨n + 1, le_refl _, h⟩
        · rintro ⟨d, hd, hc⟩
          rcases hd.eq_or_lt with rfl | hlt
          · exact Or.inr hc
          · exact Or.inl ⟨d, Nat.lt_succ_iff.mp hlt, hc⟩
  refine ComputablePred.computable_iff.mpr ⟨_, hS, funext λ a ↦ propext ?_⟩
  rw [key (bd a) (cd a)]
  exact exists_congr λ d ↦ and_congr_right λ _ ↦ (congrFun hχe (d, cd a)).to_iff

/-- The Ehrenfeucht–Mycielski speedup theorem [EM71]. -/
theorem ehrenfeucht_mycielski_speedup [L.DecidableEq] [L.Primcodable]
  (hU : ¬ComputablePred (insert (∼σ) T).theory) :
  ¬∃ f : ℕ → ℕ,
    Computable f ∧
    ∀ π : Sentence L, T ⊢ π → T.minProof π ≤ f ((insert σ T).minProof π) := by
  rintro ⟨f, hf_comp, hf_bound⟩
  apply hU
  refine ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm)
  refine ComputablePred.of_eq
    (computablePred_bddExists_proof (T := T)
      (bd := λ π ↦ f ((insert σ T).minProof (σ ⋎ π))) (cd := λ π ↦ encode (σ ⋎ π))
      (hf_comp.comp computable_insert_minProof_or) (Computable.encode.comp computable_or_left))
    λ π ↦ ?_
  constructor
  · rintro ⟨d, _, hd⟩
    exact Provable.sound (⟨d, by rwa [Sentence.quote_eq_encode_nat]⟩ : Provable T (⌜σ ⋎ π⌝ : ℕ))
  · intro h
    exact ⟨T.minProof (σ ⋎ π), hf_bound (σ ⋎ π) h, by
      have := proof_minProof h
      rwa [Sentence.quote_eq_encode_nat] at this⟩

lemma exists_lt_minProof [L.DecidableEq] [L.Primcodable]
    (hU : ¬ComputablePred (insert (∼σ) T).theory) {f : ℕ → ℕ} (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π := by
  by_contra h
  push Not at h
  exact ehrenfeucht_mycielski_speedup hU ⟨f, hf, h⟩

theorem ehrenfeucht_mycielski_speedup_arithmetic {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] :
    ¬∃ f : ℕ → ℕ, Computable f ∧
      ∀ π : ArithmeticSentence, T ⊢ π → T.minProof π ≤ f ((insert σ T).minProof π) :=
  have : 𝗥₀ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗥₀ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T))
  ehrenfeucht_mycielski_speedup (church_theorem_general (insert (∼σ) T))

lemma exists_lt_minProof_arithmetic {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] {f : ℕ → ℕ} (hf : Computable f) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗥₀ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗥₀ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T))
  exists_lt_minProof (church_theorem_general (insert (∼σ) T)) hf

example {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π) := by
  have hcomp : Computable λ x : ℕ ↦ 2 ^ (x + 1) :=
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ).to_comp
  obtain ⟨π, hπ, hlt⟩ := exists_lt_minProof_arithmetic (T := T) (σ := σ) hcomp
  exact ⟨π, hπ, (Nat.le_log_iff_pow_le (b := 2) (by norm_num)
    (((Nat.zero_le _).trans_lt hlt).ne')).mpr hlt.le⟩

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
