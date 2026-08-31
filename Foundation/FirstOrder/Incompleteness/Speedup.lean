module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Primrec
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce
public import Mathlib.Data.Nat.Log

/-!
# Ehrenfeucht–Mycielski speedup theorem

`Theory.minProof T σ` is the least Gödel code of a proof of `σ` in `T`, and `0` when `σ` is not
`T`-provable.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

section Provability

variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or : insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨λ h ↦ by cl_prover [h], λ h ↦ by cl_prover [h]⟩

end Provability

variable
  {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
  {T : Theory L} [T.Δ₁] {σ : Sentence L}

/-- The least Gödel code of a proof object `T ⊢! σ`, or zero if no such object exists. -/
noncomputable def _root_.LO.FirstOrder.Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ :=
  sInf (Set.range λ d : T ⊢! σ ↦ (⌜d⌝ : ℕ))

@[grind →]
lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) ⌜σ⌝ := by
  obtain ⟨b, hb⟩ : T.minProof σ ∈ Set.range (λ d : T ⊢! σ ↦ (⌜d⌝ : ℕ)) :=
    Nat.sInf_mem ⟨_, Set.mem_range_self h.get⟩
  exact hb ▸ proof_of_quote_proof b

@[grind →]
lemma minProof_eq_zero_of_unprovable (h : T ⊬ σ) : T.minProof σ = 0 := by
  simp [Theory.minProof, Set.range_eq_empty_iff.mpr (Entailment.unprovable_iff_isEmpty.mp h)]

@[grind ←]
lemma minProof_le (b : T ⊢! σ) : T.minProof σ ≤ ⌜b⌝ := Nat.sInf_le (Set.mem_range_self b)

open Encodable

variable {α : Type*} [Primcodable α] {F : α → Sentence L}

omit [L.DecidableEq] in
lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr;
  obtain ⟨φ, hφ⟩ := HierarchySymbol.Definable.of_delta (Γ := 𝚺) (Proof.definable (V := ℕ) (T := T));
  obtain ⟨ψ, hψ⟩ :=
    (HierarchySymbol.Definable.of_delta (Γ := 𝚷) (Proof.definable (V := ℕ) (T := T))).notPi;
  have hcomp : Computable λ p : ℕ × ℕ ↦ p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil :=
    Primrec.to_comp <|
    Primrec.vector_cons.comp .fst (Primrec.vector_cons.comp .snd (.const List.Vector.nil));
  exact ⟨((sigma1_re id φ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hφ.iff (v := ![p.1, p.2]),
    ((sigma1_re id ψ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hψ.iff (v := ![p.1, p.2])⟩;

omit [L.DecidableEq] in
lemma computablePred_bddExists_proof [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
    (hbd : Computable bd) :
    ComputablePred λ a ↦ ∃ d ≤ bd a, Proof T d ⌜F a⌝ := by
  set cd := λ a ↦ encode (F a);
  have hcd : Computable cd := Computable.encode.comp hF;
  obtain ⟨χ, hχ, hχe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T));
  have hstep : Computable (λ q : α × (ℕ × Bool) ↦ Bool.or q.2.2 (χ (q.2.1, cd q.1))) :=
    Computable₂.comp Primrec.or.to_comp (Computable.snd.comp Computable.snd)
      (hχ.comp (Computable.pair (Computable.fst.comp Computable.snd) (hcd.comp Computable.fst)));
  have hS : Computable λ a ↦
      Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, cd a)) (bd a + 1) :=
    Computable.nat_rec (Computable.succ.comp hbd) (Computable.const false) hstep.to₂;
  refine ComputablePred.computable_iff.mpr ⟨_, hS, ?_⟩;
  . funext a;
    apply propext;
    have key : ∀ N e,
        (Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, e)) (N + 1) = true)
          ↔ ∃ d ≤ N, χ (d, e) = true := by
      intro N e;
      induction N with
      | zero => simp;
      | succ n ih => grind;
    rw [key (bd a) (cd a), Sentence.quote_eq_encode_nat];
    exact exists_congr λ d ↦ and_congr_right λ _ ↦ (congrFun hχe (d, cd a)).to_iff;

lemma computablePred_provable_of_minProof_le [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
    (hbd : Computable bd) (hb : ∀ a, T ⊢ F a → T.minProof (F a) ≤ bd a) :
    ComputablePred λ a ↦ T ⊢ F a := by
  apply ComputablePred.of_eq (computablePred_bddExists_proof (T := T) hF hbd);
  intro a;
  have hp : ∀ d, Proof T d ⌜F a⌝ → T ⊢ F a := λ d hd ↦ provable_iff_provable.mp ⟨d, hd⟩;
  grind;

private def speedupDerivation (φ ψ : Proposition L) : ⊢ᴸᴷ¹ [φ ⋎ ψ, ∼φ] :=
  Derivation.or (Derivation.eta φ).contra

private def speedupProof (T : Theory L) (σ π : Sentence L) : insert σ T ⊢! σ ⋎ π where
  axioms := [σ]
  axioms_mem := by simp
  derivation := .cast (speedupDerivation ↑σ ↑π)

section Code

variable {s p q d : α → ℕ}

private noncomputable def cutAxmCode (cΓ cφ cd : ℕ) : ℕ :=
  cutRule cΓ cφ (axm (insert cφ cΓ) cφ) cd

private noncomputable def speedupCode (cσ cnσ cπ cor cd : ℕ) : ℕ :=
  cutAxmCode (insert cor ∅) cσ
    (orIntro (insert cor (insert cnσ ∅)) cσ cπ
      (wkRule (insert cσ (insert cπ (insert cor (insert cnσ ∅))))
        (wkRule (insert cσ (insert cπ (insert cnσ ∅))) cd)))

private lemma primrec_cutAxmCode (hs : Primrec s) (hp : Primrec p) (hd : Primrec d) :
    Primrec λ x ↦ cutAxmCode (s x) (p x) (d x) :=
  primrec_cutRule hs hp (primrec_axm (primrec_insert hp hs) hp) hd

private lemma primrec_speedupCode (hp : Primrec p) (hq : Primrec q) (cσ cnσ cd : ℕ) :
    Primrec λ x ↦ speedupCode cσ cnσ (p x) (q x) cd := by
  have h₁ : Primrec λ x ↦ (insert (q x) ∅ : ℕ) := primrec_insert hq (.const ∅);
  have h₂ : Primrec λ x ↦ (insert (q x) (insert cnσ ∅) : ℕ) := primrec_insert hq (.const _);
  have h₃ : Primrec λ x ↦ (insert cσ (insert (p x) (insert cnσ ∅)) : ℕ) :=
    primrec_insert (.const cσ) (primrec_insert hp (.const _));
  have h₄ : Primrec λ x ↦ (insert cσ (insert (p x) (insert (q x) (insert cnσ ∅))) : ℕ) :=
    primrec_insert (.const cσ) (primrec_insert hp h₂);
  exact primrec_cutAxmCode h₁ (.const cσ)
    (primrec_orIntro h₂ (.const cσ) hp (primrec_wkRule h₄ (primrec_wkRule h₃ (.const cd))));

end Code

section Quotation

variable {φ ψ : Sentence L} {χ ξ : Proposition L}

private lemma quote_cutManyProof_singleton (hψ : ∀ χ ∈ [ψ], χ ∈ T)
    (e : T ⟹₂ insert (φ : Proposition L) (∼Sequent.embed [ψ]).toFinset) :
    (⌜Derivation2.cutManyProof [ψ] hψ e⌝ : ℕ)
      = cutAxmCode ⌜insert (φ : Proposition L) (∅ : Finset (Proposition L))⌝ ⌜ψ⌝ ⌜e⌝ := by
  have h : (⌜Derivation2.cutManyProof [ψ] hψ e⌝ : ℕ)
      = ⌜Derivation2.cut (Γ := insert (φ : Proposition L) (∅ : Finset (Proposition L)))
            (φ := (ψ : Proposition L)) (Derivation2.axm ψ (hψ ψ (by simp)) (by simp))
            (Derivation2.cast e (by ext x; simp [Sequent.embed]; grind))⌝ := rfl;
  rw [h, Derivation2.quote_cut, Derivation2.quote_axm, Derivation2.quote_cast];
  simp [cutAxmCode, Sentence.quote_def];

private lemma quote_proof_eq (b : T ⊢! φ) (h : b.axioms = [ψ]) :
    (⌜b⌝ : ℕ)
      = cutAxmCode ⌜insert (φ : Proposition L) (∅ : Finset (Proposition L))⌝ ⌜ψ⌝
          ⌜Derivation.toDerivation2 T b.derivation⌝ := by
  obtain ⟨A, hA, d⟩ := b;
  subst h;
  rw [quote_proof_def];
  have h : (⌜(⟨[ψ], hA, d⟩ : T ⊢! φ).toProof2⌝ : ℕ)
      = ⌜Derivation2.cutManyProof [ψ] hA
          ((Derivation2.cast (Derivation.toDerivation2 T d)
              (by ext x; simp [List.toFinset_cons, Sequent.embed]) :
            T ⟹₂ insert (φ : Proposition L) (∼Sequent.embed [ψ]).toFinset))⌝ := rfl;
  rw [h, quote_cutManyProof_singleton, Derivation2.quote_cast];

private lemma quote_pullback_cast {A : List (Sentence L)} {Γ : List (Proposition L)}
    (d : ⊢ᴸᴷ¹ Γ) (h : Γ = A.map Rewriting.emb) :
    (⌜Derivation.toDerivation2 T (OneSidedLK.Pullback.cast d h)⌝ : ℕ)
      = ⌜Derivation.toDerivation2 T d⌝ := by
  subst h; rfl;

private lemma quote_speedupDerivation :
    (⌜Derivation.toDerivation2 T (speedupDerivation χ ξ)⌝ : ℕ)
      = orIntro ⌜([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset⌝ ⌜χ⌝ ⌜ξ⌝
          (wkRule ⌜insert χ (insert ξ ([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset)⌝
            (wkRule ⌜([χ, ξ, ∼χ] : List (Proposition L)).toFinset⌝
              ⌜Derivation.toDerivation2 T (Derivation.eta χ)⌝)) := by
  have h : (⌜Derivation.toDerivation2 T (speedupDerivation χ ξ)⌝ : ℕ)
      = ⌜Derivation2.or (Γ := ([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset)
          (φ := χ) (ψ := ξ) (by simp)
          (Derivation2.wk
            (Derivation2.wk (Γ := ([χ, ξ, ∼χ] : List (Proposition L)).toFinset)
              (Derivation.toDerivation2 T (Derivation.eta χ)) (by simp)) (by simp))⌝ := rfl;
  rw [h, Derivation2.quote_or, Derivation2.quote_wk, Derivation2.quote_wk];

private lemma quote_speedupProof_eq (π : Sentence L) :
    (⌜speedupProof T σ π⌝ : ℕ)
      = speedupCode ⌜σ⌝ ⌜∼σ⌝ ⌜π⌝ ⌜σ ⋎ π⌝
          ⌜Derivation.toDerivation2 (insert σ T) (Derivation.eta (σ : Proposition L))⌝ := by
  rw [quote_proof_eq (speedupProof T σ π) rfl];
  have h : (⌜Derivation.toDerivation2 (insert σ T) (speedupProof T σ π).derivation⌝ : ℕ)
      = ⌜Derivation.toDerivation2 (insert σ T)
          (speedupDerivation (σ : Proposition L) (π : Proposition L))⌝ :=
    quote_pullback_cast _ _;
  rw [h, quote_speedupDerivation];
  simp [speedupCode, Sentence.quote_def];

end Quotation

private lemma computable_quote_speedupProof [L.Primcodable] :
    Computable λ π ↦ (⌜speedupProof T σ π⌝ : ℕ) := by
  have hp : Primrec λ π : Sentence L ↦ (⌜π⌝ : ℕ) :=
    Primrec.encode.of_eq λ π ↦ (Sentence.quote_eq_encode_nat π).symm;
  have hq : Primrec λ π : Sentence L ↦ (⌜σ ⋎ π⌝ : ℕ) :=
    (Primrec.encode.comp (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id)).of_eq
      λ π ↦ (Sentence.quote_eq_encode_nat _).symm;
  exact Primrec.to_comp <|
    (primrec_speedupCode hp hq ⌜σ⌝ ⌜∼σ⌝
      ⌜Derivation.toDerivation2 (insert σ T) (Derivation.eta (σ : Proposition L))⌝).of_eq
      λ π ↦ (quote_speedupProof_eq π).symm;

private lemma exists_computable_bound_minProof_or [L.Primcodable] :
    ∃ c : Sentence L → ℕ, Computable c ∧ ∀ π, (insert σ T).minProof (σ ⋎ π) ≤ c π :=
  ⟨λ π ↦ ⌜speedupProof T σ π⌝, computable_quote_speedupProof,
    λ π ↦ minProof_le (speedupProof T σ π)⟩

/-- The Ehrenfeucht–Mycielski speedup theorem.

- [EM71] -/
theorem ehrenfeucht_mycielski_speedup [L.Primcodable]
    (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π := by
  contrapose! hU;
  obtain ⟨c, hc, hcb⟩ := exists_computable_bound_minProof_or (T := T) (σ := σ);
  refine ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm);
  exact computablePred_provable_of_minProof_le
    (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp
    ((Nat.computable_boundedMax hf).comp hc)
    λ π hπ ↦ (hU (σ ⋎ π) hπ).trans (Nat.le_boundedMax (hcb π));

section Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

theorem ehrenfeucht_mycielski_speedup_arithmetic (hσ : T ⊬ σ) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗜𝚺₁ ⪯ insert (∼σ) T :=
    Entailment.WeakerThan.trans ‹𝗜𝚺₁ ⪯ T›
      (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T));
  have : Entailment.Consistent (insert (∼σ) T) :=
    Entailment.unprovable_iff_consistent_adjoin.mp hσ;
  ehrenfeucht_mycielski_speedup
    (uncomputable_theory_of_consistent : ¬ComputablePred (insert (∼σ) T).theory) f hf

example (hσ : T ⊬ σ) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π) := by
  obtain ⟨π, hπ, hlt⟩ := ehrenfeucht_mycielski_speedup_arithmetic hσ (λ x ↦ 2 ^ (x + 1))
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ).to_comp);
  refine ⟨π, hπ, (Nat.le_log_iff_pow_le ?_ ?_).mpr ?_⟩;
  all_goals grind;

end Arithmetic

end LO.FirstOrder.Arithmetic.Bootstrapping
