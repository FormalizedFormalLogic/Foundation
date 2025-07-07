import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.R0.Representation

/-!
# Gödel's first incompleteness theorem for arithmetic theories stronger than $\mathsf{R_0}$
-/

namespace LO.FirstOrder.Arith

lemma re_iff_sigma1 {P : ℕ → Prop} : REPred P ↔ 𝚺₁-Predicate P := by
  constructor
  · intro h
    exact ⟨.mkSigma (codeOfREPred P) (by simp [codeOfREPred, codeOfPartrec']), by
      intro v; symm; simp; simpa [←Matrix.fun_eq_vec_one] using codeOfREPred_spec h (x := v 0)⟩
  · rintro ⟨φ, hφ⟩
    have : REPred fun x ↦ (Semiformula.Evalm ℕ (x ::ᵥ List.Vector.nil).get id) _ :=
      (sigma1_re id (φ.sigma_prop)).comp
        (f := fun x : ℕ ↦ x ::ᵥ List.Vector.nil) (Primrec.to_comp <| Primrec.vector_cons.comp .id (.const _))
    exact this.of_eq <| by intro x; symm; simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![x]

open LO.Entailment FirstOrder Arith R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

/-- Gödel's first incompleteness theorem-/
theorem goedel_first_incompleteness
    (T : ArithmeticTheory) [𝐑₀ ⪯ T] [T.Sigma1Sound] [T.Delta1Definable] :
    ¬Entailment.Complete (T : Axiom ℒₒᵣ) := by
  have con : Consistent (T : Axiom ℒₒᵣ) := inferInstance
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
  let σ : Semisentence ℒₒᵣ 1 := codeOfREPred D
  let ρ : Sentence ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢!. σ/[↑n] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁, Axiom.provable_iff] using re_complete (T := T) D_re (x := n)
  have : T ⊢!. ∼ρ ↔ T ⊢!. ρ := by
    have : T ⊢! ∼↑σ/[↑(Encodable.encode σ)] ↔ T ⊢! ↑σ/[↑(Encodable.encode σ)] := by
      simpa [Axiom.provable_iff, quote_eq_encode,
        goedelNumber'_eq_coe_encode, D, Rewriting.embedding_substs_eq_substs_coe₁] using this ⌜σ⌝
    simpa [Axiom.provable_iff, ρ, Rewriting.embedding_substs_eq_substs_coe₁]
  refine incomplete_iff_exists_undecidable.mpr
    ⟨ ρ
    , fun h ↦ not_consistent_iff_inconsistent.mpr
        (inconsistent_of_provable_of_unprovable h (this.mpr h)) inferInstance
    , fun h ↦ not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable (this.mp h) h) inferInstance ⟩

end LO.FirstOrder.Arith
