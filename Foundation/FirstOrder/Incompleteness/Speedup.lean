module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce

/-!
# Ehrenfeucht–Mycielski speedup theorem

This file defines `Theory.minProof T σ`, the least code of a `T`-proof of `σ` (`0` when `σ` is
not `T`-provable), and formalizes the Ehrenfeucht–Mycielski speedup theorem (1971): adjoining a
sentence `σ` to `T` gives an unbounded proof-length speedup over `T` whenever `T + ∼σ` is not
decidable.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

section
variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or :
    insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨fun h ↦ by cl_prover [h], fun h ↦ by cl_prover [h]⟩

end

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

variable (T)

noncomputable def _root_.LO.FirstOrder.Theory.minProof (σ : Sentence L) : ℕ :=
  sInf {d : ℕ | Proof T d (⌜σ⌝ : ℕ)}

variable {T} {σ : Sentence L}

lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) (⌜σ⌝ : ℕ) :=
  Nat.sInf_mem (internalize_provability (V := ℕ) h)

lemma minProof_eq_zero_of_unprovable [L.DecidableEq] (h : T ⊬ σ) : T.minProof σ = 0 :=
  Nat.sInf_eq_zero.mpr <| .inr <| Set.eq_empty_iff_forall_notMem.mpr fun d hd ↦
    h (Provable.sound (⟨d, hd⟩ : Provable T (⌜σ⌝ : ℕ)))

lemma minProof_le {d} (h : Proof T d (⌜σ⌝ : ℕ)) : T.minProof σ ≤ d :=
  Nat.sInf_le h

section Speedup

open Encodable

lemma computablePred_proof : ComputablePred fun p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  obtain ⟨φ, hφ⟩ := HierarchySymbol.Definable.of_delta (Γ := 𝚺) (Proof.definable (V := ℕ) (T := T))
  obtain ⟨ψ, hψ⟩ :=
    (HierarchySymbol.Definable.of_delta (Γ := 𝚷) (Proof.definable (V := ℕ) (T := T))).notPi
  have hcomp : Computable fun p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.to_comp <|
      Primrec.vector_cons.comp .fst (Primrec.vector_cons.comp .snd (.const List.Vector.nil))
  exact ⟨((sigma1_re id φ.sigma_prop).comp hcomp).of_eq
      fun p ↦ by simpa [List.Vector.cons_get] using hφ.iff (v := ![p.1, p.2]),
    ((sigma1_re id ψ.sigma_prop).comp hcomp).of_eq
      fun p ↦ by simpa [List.Vector.cons_get] using hψ.iff (v := ![p.1, p.2])⟩

lemma computable_minProof_comp [L.Primcodable] {α : Type*} [Primcodable α] {F : α → Sentence L}
    (hF : Computable F) (hprov : ∀ a, T ⊢ F a) :
    Computable fun a ↦ T.minProof (F a) := by
  classical
  have hex : ∀ a, ∃ d, Proof T d (⌜F a⌝ : ℕ) :=
    fun a ↦ ⟨T.minProof (F a), proof_minProof (hprov a)⟩
  have hcomp : ComputablePred fun p : α × ℕ ↦ Proof T p.2 (⌜F p.1⌝ : ℕ) := by
    obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T))
    refine ComputablePred.computable_iff.mpr
      ⟨fun p ↦ f (p.2, encode (F p.1)),
        hf.comp (Computable.pair Computable.snd (Computable.encode.comp (hF.comp Computable.fst))),
        funext fun p ↦ ?_⟩
    simp only [Sentence.quote_eq_encode_nat]
    exact congrFun hfe (p.2, encode (F p.1))
  exact (Computable.find hcomp hex).of_eq fun a ↦ (Nat.sInf_def (hex a)).symm

omit [L.LORDefinable] in
lemma computable_or_left [L.Primcodable] : Computable fun π : Sentence L ↦ σ ⋎ π := by
  set b : ℕ := encode σ with hb
  have hCode : Primrec fun e : ℕ ↦ (Nat.pair 5 <| b.pair e) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
      (Primrec₂.natPair.comp (Primrec.const b) Primrec.id))
  refine (Computable.ofOption ((Computable.decode (α := Sentence L)).comp
    (hCode.to_comp.comp Computable.encode))).of_eq_tot fun π ↦ ?_
  have he : (Nat.pair 5 <| b.pair (encode π)) + 1 = encode (σ ⋎ π) := by rw [hb]; rfl
  simp [he, Encodable.encodek]

lemma computable_insert_minProof_or [L.DecidableEq] [L.Primcodable] :
    Computable fun π : Sentence L ↦ (insert σ T).minProof (σ ⋎ π) :=
  computable_minProof_comp (T := insert σ T) computable_or_left
    fun π ↦ Entailment.deduction_iff.mpr (by cl_prover)

lemma computablePred_bddExists_proof {α : Type*} [Primcodable α] {bd cd : α → ℕ}
    (hbd : Computable bd) (hcd : Computable cd) :
    ComputablePred fun a : α ↦ ∃ d ≤ bd a, Proof T d (cd a) := by
  obtain ⟨χ, hχ, hχe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T))
  have hstep : Computable (fun q : α × (ℕ × Bool) ↦ Bool.or q.2.2 (χ (q.2.1, cd q.1))) :=
    Computable₂.comp Primrec.or.to_comp (Computable.snd.comp Computable.snd)
      (hχ.comp (Computable.pair (Computable.fst.comp Computable.snd) (hcd.comp Computable.fst)))
  have hS : Computable fun a : α ↦
      Nat.rec (motive := fun _ ↦ Bool) false (fun d ih ↦ ih || χ (d, cd a)) (bd a + 1) :=
    Computable.nat_rec (Computable.succ.comp hbd) (Computable.const false) hstep.to₂
  have key : ∀ N e, (Nat.rec (motive := fun _ ↦ Bool) false (fun d ih ↦ ih || χ (d, e)) (N + 1) = true) ↔
      ∃ d ≤ N, χ (d, e) = true := by
    intro N e
    induction N with
    | zero => simp
    | succ n ih =>
        show ((Nat.rec (motive := fun _ ↦ Bool) false (fun d ih ↦ ih || χ (d, e)) (n + 1)) ||
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
  refine ComputablePred.computable_iff.mpr ⟨_, hS, funext fun a ↦ propext ?_⟩
  rw [key (bd a) (cd a)]
  exact exists_congr fun d ↦ and_congr_right fun _ ↦ (congrFun hχe (d, cd a)).to_iff

/-- The Ehrenfeucht–Mycielski speedup theorem: if the set of `T + ∼σ`-provable sentences is not
computable, then adjoining `σ` to `T` as a new axiom gives an unbounded proof-length speedup over
`T`, in the sense that no computable monotone function bounds the minimal `T`-proof code of a
`T`-provable `π` in terms of the minimal `(T + σ)`-proof code of `π`.
- [EM71, Theorem] -/
theorem ehrenfeucht_mycielski_speedup [L.DecidableEq] [L.Primcodable]
  (hU : ¬ComputablePred fun π : Sentence L ↦ insert (∼σ) T ⊢ π) :
  ¬∃ s : ℕ → ℕ,
    Computable s ∧
    Monotone s ∧
    ∀ π : Sentence L, T ⊢ π → T.minProof π ≤ s ((insert σ T).minProof π) := by
  rintro ⟨s, hs_comp, -, hs_bound⟩
  apply hU
  refine ComputablePred.of_eq ?_ (fun π ↦ provable_insert_neg_iff_or.symm)
  refine ComputablePred.of_eq
    (computablePred_bddExists_proof (T := T)
      (bd := fun π ↦ s ((insert σ T).minProof (σ ⋎ π))) (cd := fun π ↦ encode (σ ⋎ π))
      (hs_comp.comp computable_insert_minProof_or) (Computable.encode.comp computable_or_left))
    fun π ↦ ?_
  constructor
  · rintro ⟨d, _, hd⟩
    exact Provable.sound (⟨d, by rwa [Sentence.quote_eq_encode_nat]⟩ : Provable T (⌜σ ⋎ π⌝ : ℕ))
  · intro h
    exact ⟨T.minProof (σ ⋎ π), hs_bound (σ ⋎ π) h, by
      have := proof_minProof h
      rwa [Sentence.quote_eq_encode_nat] at this⟩

/-- The hypothesis `hU` in `ehrenfeucht_mycielski_speedup` is automatically satisfied when `T` is
an arithmetic theory extending `𝗥₀` and sound on `𝚺₁` sentences, by Church's theorem. -/
theorem ehrenfeucht_mycielski_speedup' {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] :
    ¬∃ s : ℕ → ℕ,
      Computable s ∧
      Monotone s ∧
      ∀ π : ArithmeticSentence, T ⊢ π → T.minProof π ≤ s ((insert σ T).minProof π) :=
  have : 𝗥₀ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗥₀ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T))
  ehrenfeucht_mycielski_speedup (church_theorem_general (T := insert (∼σ) T))

theorem ehrenfeucht_mycielski_speedup_exp [L.DecidableEq] [L.Primcodable]
    (hU : ¬ComputablePred fun π : Sentence L ↦ insert (∼σ) T ⊢ π) :
    ∃ π : Sentence L, T ⊢ π ∧ 2 ^ ((insert σ T).minProof π) < T.minProof π := by
  have hcomp : Computable fun x : ℕ ↦ 2 ^ x :=
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id).to_comp
  have hmono : Monotone fun x : ℕ ↦ 2 ^ x := fun _ _ hab ↦ Nat.pow_le_pow_right (by norm_num) hab
  have h : ¬∀ π : Sentence L, T ⊢ π → T.minProof π ≤ 2 ^ ((insert σ T).minProof π) :=
    fun h ↦ ehrenfeucht_mycielski_speedup hU ⟨_, hcomp, hmono, h⟩
  push Not at h
  exact h

/-- There is a `T`-provable sentence whose `T`-proof code is exponentially longer than its
`(T + σ)`-proof code. -/
theorem ehrenfeucht_mycielski_speedup_exp' {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence}
    [𝗥₀ ⪯ T] [(insert (∼σ) T).SoundOnHierarchy 𝚺 1] :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ 2 ^ ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗥₀ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗥₀ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T))
  ehrenfeucht_mycielski_speedup_exp (church_theorem_general (T := insert (∼σ) T))

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
