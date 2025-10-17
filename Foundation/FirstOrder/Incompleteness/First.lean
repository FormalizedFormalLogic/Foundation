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
    IsSemiformula ℒₒᵣ 1 φ ∧ T.Provable (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ)
  have D_re : REPred D := by
    have : 𝚺₁-Predicate fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧ T.Provable (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ) := by
      definability
    exact re_iff_sigma1.mpr this
  have D_spec (φ : Semisentence ℒₒᵣ 1) : D ⌜φ⌝ ↔ T ⊢ ∼φ/[⌜φ⌝] := by
    simp [D, ←provable_iff_provable, Sentence.quote_def,
      Rewriting.emb_subst_eq_subst_coe₁, Semiformula.quote_def]
  let δ : Semisentence ℒₒᵣ 1 := codeOfREPred D
  have (n : ℕ) : D n ↔ T ⊢ δ/[↑n] := by
    simpa [Semiformula.coe_subst_eq_subst_coe₁] using re_complete D_re
  let π : Sentence ℒₒᵣ := δ/[⌜δ⌝]
  have : T ⊢ π ↔ T ⊢ ∼π := calc
    T ⊢ π ↔ T ⊢ δ/[⌜δ⌝]  := by rfl
    _     ↔ D ⌜δ⌝        := by simpa using (this ⌜δ⌝).symm
    _     ↔ T ⊢ ∼δ/[⌜δ⌝] := D_spec δ
    _     ↔ T ⊢ ∼π       := by rfl
  refine incomplete_def.mpr ⟨π, ?_, ?_⟩
  · intro h
    exact not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable h (this.mp h)) inferInstance
  · intro h
    exact not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable (this.mpr h) h) inferInstance

theorem exists_true_but_unprovable_sentence
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : Sentence ℒₒᵣ, ℕ ⊧ₘ δ ∧ T ⊬ δ := by
  obtain ⟨δ, hδ⟩ := incomplete_def.mp $ Arithmetic.incomplete T;
  by_cases ℕ ⊧ₘ δ
  . exact ⟨δ, by assumption, hδ.1⟩
  . exact ⟨∼δ, by simpa, hδ.2⟩

end LO.FirstOrder.Arithmetic

namespace LO.FirstOrderTrueArith

open LO.Entailment FirstOrder Arithmetic

instance {T : ArithmeticTheory} [ℕ ⊧ₘ* T] [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⪱ 𝗧𝗔 := by
  constructor;
  . infer_instance
  . obtain ⟨δ, δTrue, δUnprov⟩ := exists_true_but_unprovable_sentence T;
    exact Entailment.not_weakerThan_iff.mpr ⟨δ, FirstOrderTrueArith.provable_iff.mpr δTrue, δUnprov⟩

end LO.FirstOrderTrueArith
