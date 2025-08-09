import Foundation.FirstOrder.Incompleteness.First
import Mathlib.Computability.Reduce

/-!
  # Church's Undecidability of First-Order Logic Theorem
-/


section

variable {α β} [Primcodable α] [Primcodable β]

lemma ComputablePred.range_subset  {f : α → β} (hf : Computable f) {A} (hA : ComputablePred A) : ComputablePred { x | A (f x) } := by
  apply computable_iff.mpr;
  obtain ⟨inA, hinA₁, rfl⟩ := computable_iff.mp hA;
  use λ x => inA (f x);
  constructor;
  . apply Computable.comp <;> assumption;
  . rfl;

end


namespace LO.ISigma1

open Entailment FirstOrder FirstOrder.Arithmetic

variable {T : Theory ℒₒᵣ} [𝐈𝚺₁ ⪯ T] [Entailment.Consistent T]

lemma not_exists_theorem_representable_predicate : ¬∃ τ : Semisentence ℒₒᵣ 1, ∀ σ, (T ⊢!. σ → T ⊢!. τ/[⌜σ⌝]) ∧ (T ⊬. σ → T ⊢!. ∼τ/[⌜σ⌝]) := by
  rintro ⟨τ, hτ⟩;
  have ⟨h₁, h₂⟩ := hτ $ fixpoint “x. ¬!τ x”;
  by_cases h : T ⊢!. fixpoint (∼τ/[#0]);
  . apply Entailment.Consistent.not_bot (𝓢 := T.toAxiom);
    . infer_instance;
    . have H₁ : T ⊢!. τ/[⌜fixpoint (∼τ/[#0])⌝] := h₁ h;
      have H₂ : T ⊢!. fixpoint (∼τ/[#0]) ⭤ ∼τ/[⌜fixpoint (∼τ/[#0])⌝] := by simpa using diagonal “x. ¬!τ x”;
      cl_prover [h, H₁, H₂];
  . apply h;
    have H₁ : T ⊢!. ∼τ/[⌜fixpoint (∼τ/[#0])⌝] := h₂ h;
    have H₂ : T ⊢!. fixpoint (∼τ/[#0]) ⭤ ∼τ/[⌜fixpoint (∼τ/[#0])⌝] := by simpa using diagonal “x. ¬!τ x”;
    cl_prover [H₁, H₂];

end LO.ISigma1


namespace LO.FirstOrder

open LO.Entailment
open ISigma1 FirstOrder FirstOrder.Arithmetic

section

variable {L : Language} {T : Theory L} {σ : Sentence L}

@[simp] lemma Theory.eq_empty_toAxiom_empty : (∅ : Theory L).toAxiom = ∅ := by simp [Theory.toAxiom];

noncomputable def Theory.finite_conjunection (T_finite : T.Finite) : Sentence L :=
  letI A := T.toAxiom;
  haveI A_finite : A.Finite := by apply Set.Finite.image; simpa;
  A_finite.toFinset.conj

lemma iff_axiomProvable_empty_context_provable {A : Axiom L} : A ⊢! σ ↔ A *⊢[(∅ : Axiom L)]! σ := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

lemma iff_provable₀_empty_context_provable : T ⊢!. σ ↔ (T.toAxiom) *⊢[(∅ : Theory L).toAxiom]! σ := by
  apply Iff.trans iff_axiomProvable_empty_context_provable;
  simp;

variable [DecidableEq (Sentence L)]

lemma firstorder_provable_of_finite_provable (T_finite : T.Finite) : T ⊢!. σ ↔ ∅ ⊢!. (Theory.finite_conjunection T_finite) ➝ σ := by
  apply Iff.trans ?_ FConj_DT.symm;
  apply Iff.trans iff_provable₀_empty_context_provable;
  simp;

end

namespace Arithmetic

variable {T : ArithmeticTheory} [𝐈𝚺₁ ⪯ T] [Entailment.Consistent T] [T.SoundOnHierarchy 𝚺 1]
variable {σ : Sentence _}

open Classical in
/-- Godel number of theorems of `T` is not computable. -/
theorem not_computable_theorems : ¬ComputablePred (fun n : ℕ ↦ ∃ σ : Sentence ℒₒᵣ, n = ⌜σ⌝ ∧ T ⊢!. σ) := by
  by_contra hC;
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ σ : Semisentence ℒₒᵣ 1, n = ⌜σ⌝ ∧ T ⊬. σ/[⌜σ⌝];
  have : ComputablePred D := by
    let f : ℕ → ℕ := λ n => if h : ∃ σ : Semisentence ℒₒᵣ 1, n = ⌜σ⌝ then ⌜(h.choose/[⌜h.choose⌝] : Sentence ℒₒᵣ)⌝ else 0;
    have : ComputablePred (λ x => ¬∃ σ, f x = ⌜σ⌝ ∧ T ⊢!. σ) := ComputablePred.range_subset (f := f) (by sorry) (ComputablePred.not hC);
    sorry;
  simpa [D] using re_complete (T := T) (ComputablePred.to_re this) (x := ⌜(codeOfREPred D)⌝);

open Classical in
/-- Godel number of theorems of first-order logic on `ℒₒᵣ` is not computable. -/
theorem firstorder_undecidability : ¬ComputablePred (fun n : ℕ ↦ ∃ σ : Sentence ℒₒᵣ, n = ⌜σ⌝ ∧ ∅ ⊢!. σ) := by
  by_contra h;
  apply @not_computable_theorems (T := 𝐏𝐀⁻) (by sorry) inferInstance inferInstance;
  sorry;

end Arithmetic

end LO.FirstOrder
