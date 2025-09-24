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

open LO.Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

/-- Gödel's first incompleteness theorem-/
theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    Incomplete T := by
  have con : Consistent T := inferInstance
  let D : ℕ → Prop := fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧ T.Provable (neg ℒₒᵣ <| substs ℒₒᵣ ?[numeral φ] φ)
  have D_re : REPred D := by
    have : 𝚺₁-Predicate fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧ T.Provable (neg ℒₒᵣ <| substs ℒₒᵣ ?[numeral φ] φ) := by
      definability
    exact re_iff_sigma1.mpr this
  let σ : Semisentence ℒₒᵣ 1 := codeOfREPred D
  let ρ : Sentence ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢ σ/[↑n] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁] using re_complete D_re
  have : T ⊢ ∼ρ ↔ T ⊢ ρ := by
    have : T.Provable (neg ℒₒᵣ (substs ℒₒᵣ (numeral ⌜σ⌝ ∷ 0) ⌜σ⌝)) ↔ T ⊢ σ/[⌜σ⌝] := by
      simpa [D] using this ⌜σ⌝
    have : T ⊢ ∼σ/[⌜σ⌝] ↔ T ⊢ σ/[⌜σ⌝] := by
      simpa [←provable_iff_provable, Sentence.quote_def,
        Rewriting.embedding_substs_eq_substs_coe₁, Semiformula.quote_def] using this
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
  by_cases ℕ ⊧ₘ σ
  . exact ⟨σ, by assumption, hσ.1⟩
  . exact ⟨∼σ, by simpa, hσ.2⟩

end LO.FirstOrder.Arithmetic

namespace LO.FirstOrderTrueArith

open LO.Entailment FirstOrder Arithmetic

instance {T : ArithmeticTheory} [ℕ ⊧ₘ* T] [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⪱ 𝗧𝗔 := by
  constructor;
  . infer_instance
  . obtain ⟨σ, σTrue, σUnprov⟩ := exists_true_but_unprovable_sentence T;
    exact Entailment.not_weakerThan_iff.mpr ⟨σ, FirstOrderTrueArith.provable_iff.mpr σTrue, σUnprov⟩

end LO.FirstOrderTrueArith
