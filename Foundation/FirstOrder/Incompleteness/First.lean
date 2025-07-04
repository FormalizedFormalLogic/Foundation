import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.R0.Representation

/-!
# Gödel's first incompleteness theorem over $\mathsf{R_0}$

-/

namespace LO

lemma FirstOrder.Arith.re_iff_sigma1 {P : ℕ → Prop} : REPred P ↔ 𝚺₁-Predicate P := by
  constructor
  · intro h
    exact ⟨.mkSigma (codeOfREPred P) (by simp [codeOfREPred, codeOfPartrec']), by
      intro v; symm; simp; simpa [←Matrix.fun_eq_vec_one] using codeOfREPred_spec h (x := v 0)⟩
  · rintro ⟨φ, hφ⟩
    have := (sigma1_re id (φ.sigma_prop)).comp
      (f := fun x : ℕ ↦ x ::ᵥ List.Vector.nil) (Primrec.to_comp <| Primrec.vector_cons.comp .id (.const _))
    exact this.of_eq <| by intro x; symm; simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![x]

open FirstOrder Arith R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

/-- Gödel's First Incompleteness Theorem-/
theorem R0.goedel_first_incompleteness
    (T : Theory ℒₒᵣ) [𝐑₀ ⪯ T] [Sigma1Sound T] [T.Delta1Definable] : ¬Entailment.Complete T := by
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ φ : SyntacticSemiformula ℒₒᵣ 1, n = ⌜φ⌝ ∧ T ⊢! ∼φ/[⌜φ⌝]
  have D_re : REPred D := by
    have : 𝚺₁-Predicate fun φ : ℕ ↦
        ⌜ℒₒᵣ⌝.IsSemiformula 1 φ ∧
          (T.codeIn ℕ).Provable (⌜ℒₒᵣ⌝.neg <| ⌜ℒₒᵣ⌝.substs ?[Arithmetization.numeral φ] φ) := by
      definability
    exact REPred.of_eq (re_iff_sigma1.mpr this) <| by
      intro φ; constructor
      · rintro ⟨hφ, b⟩
        rcases hφ.sound with ⟨φ, rfl⟩
        refine ⟨φ, rfl, Language.Theory.Provable.sound (by simpa)⟩
      · rintro ⟨φ, rfl, b⟩
        exact ⟨by simp, by simpa using provable_of_provable (V := ℕ) b⟩
  let σ : SyntacticSemiformula ℒₒᵣ 1 := codeOfREPred (D)
  let ρ : SyntacticFormula ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢! σ/[‘↑n’] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁, Axiom.provable_iff] using re_complete (T := T) (D_re) (x := n)
  have : T ⊢! ∼ρ ↔ T ⊢! ρ := by
    simpa [D, goedelNumber'_def, quote_eq_encode] using this ⌜σ⌝
  have con : Entailment.Consistent T := consistent_of_sigma1Sound T
  refine LO.Entailment.incomplete_iff_exists_undecidable.mpr ⟨↑ρ, ?_, ?_⟩
  · intro h
    have : T ⊢! ∼↑ρ := by simpa [Axiom.provable_iff] using this.mpr h
    exact LO.Entailment.not_consistent_iff_inconsistent.mpr
      (Entailment.inconsistent_of_provable_of_unprovable h this) inferInstance
  · intro h
    have : T ⊢! ↑ρ := this.mp (by simpa [Axiom.provable_iff] using h)
    exact LO.Entailment.not_consistent_iff_inconsistent.mpr
      (Entailment.inconsistent_of_provable_of_unprovable this h) inferInstance

end LO
