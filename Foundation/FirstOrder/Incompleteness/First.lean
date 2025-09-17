import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.FirstOrder.R0.Representation

/-!
# Gödel's first incompleteness theorem for arithmetic theories stronger than $\mathsf{R_0}$
-/

namespace LO.FirstOrder.Arithmetic

lemma re_iff_sigma1 {P : ℕ → Prop} : REPred P ↔ 𝚺₁-Predicate P := by
  constructor
  · intro h
    refine ⟨.mkSigma (codeOfREPred P) (by simp [codeOfREPred, codeOfPartrec']), ?_⟩
    intro v; symm
    simpa [←Matrix.fun_eq_vec_one] using codeOfREPred_spec h (x := v 0)
  · rintro ⟨φ, hφ⟩
    have : REPred fun x ↦ (Semiformula.Evalm ℕ (x ::ᵥ List.Vector.nil).get id) _ :=
      (sigma1_re id (φ.sigma_prop)).comp
        (Primrec.to_comp <| Primrec.vector_cons.comp .id <| .const _)
    exact this.of_eq <| by intro x; symm; simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![x]

open LO.Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

/-- Gödel's first incompleteness theorem-/
theorem incomplete
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    Incomplete T := by
  have con : Consistent T := inferInstance
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ φ : Semisentence ℒₒᵣ 1, n = ⌜φ⌝ ∧ T ⊢! ∼φ/[⌜φ⌝]
  have D_re : REPred D := by
    have : 𝚺₁-Predicate fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧
          T.Provable (neg ℒₒᵣ <| substs ℒₒᵣ ?[InternalArithmetic.numeral φ] φ) := by
      definability
    exact REPred.of_eq (re_iff_sigma1.mpr this) <| by sorry
      /-
      intro φ; constructor
      · rintro ⟨hφ, b⟩
        rcases hφ.sound with ⟨φ, rfl⟩
        refine ⟨φ, rfl, Theory.Provable.sound (by simpa [Semiformula.quote_def])⟩
      · rintro ⟨φ, rfl, b⟩
        exact ⟨by simp [Semiformula.quote_def], by
          simpa [Semiformula.quote_def] using  internalize_provability (V := ℕ) b⟩
      -/
  let σ : Semisentence ℒₒᵣ 1 := codeOfREPred D
  let ρ : Sentence ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢! σ/[↑n] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁] using re_complete D_re
  have : T ⊢! ∼ρ ↔ T ⊢! ρ := by
    have : T ⊢! ∼↑σ/[↑(Encodable.encode σ)] ↔ T ⊢! ↑σ/[↑(Encodable.encode σ)] := by
      simpa [Semiformula.quote_eq_encode, Sentence.quote_eq_encode,
        goedelNumber'_eq_coe_encode, D, Rewriting.embedding_substs_eq_substs_coe₁] using this ⌜σ⌝
    simpa [ρ, Rewriting.embedding_substs_eq_substs_coe₁]
  refine incomplete_def.mpr
    ⟨ ρ
    , fun h ↦ not_consistent_iff_inconsistent.mpr
        (inconsistent_of_provable_of_unprovable h (this.mpr h)) inferInstance
    , fun h ↦ not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable (this.mp h) h) inferInstance ⟩

theorem exists_true_but_unprovable_sentence
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ σ : Sentence ℒₒᵣ, ℕ ⊧ₘ σ ∧ T ⊬ σ := by
  obtain ⟨σ, hσ⟩ := incomplete_def.mp $ Arithmetic.incomplete T;
  by_cases ℕ ⊧ₘ σ;
  . use σ;
    constructor;
    . assumption;
    . exact hσ.1;
  . use ∼σ;
    constructor;
    . simpa;
    . exact hσ.2;


end LO.FirstOrder.Arithmetic

namespace LO.FirstOrderTrueArith

open LO.Entailment FirstOrder Arithmetic

instance {T : ArithmeticTheory} [ℕ ⊧ₘ* T] [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⪱ 𝗧𝗔 := by
  constructor;
  . infer_instance
  . obtain ⟨σ, σTrue, σUnprov⟩ := exists_true_but_unprovable_sentence T;
    apply Entailment.not_weakerThan_iff.mpr;
    exact ⟨σ, FirstOrderTrueArith.provable_iff.mpr σTrue, σUnprov⟩

end LO.FirstOrderTrueArith
