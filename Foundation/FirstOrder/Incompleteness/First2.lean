import Foundation.FirstOrder.Incompleteness.First

namespace LO.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝐈𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

open LO.Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

open Classical in
/--
  If r.e. but not recursive set `A` exists, then implies incompleteness.
-/
lemma incomplete_of_REPred_not_ComputablePred' {A : Set ℕ} (hRE : REPred A) (hC : ¬ComputablePred A) :
  ∃ φ : Semisentence ℒₒᵣ 1, ∃ a : ℕ, T ⊬. φ/[a] ∧ T ⊬. ∼φ/[a] := by
  let φ := codeOfREPred A;
  use φ;
  have hA : A = { n : ℕ | T ⊢!. φ/[n] } := Set.ext fun x ↦ re_complete hRE;
  have ⟨d, hd⟩ : ∃ d : ℕ, ¬(d ∈ Aᶜ ↔ T ⊢!. ∼φ/[d]) := by
    by_contra h;
    apply hC;
    apply ComputablePred.computable_iff_re_compl_re.mpr;
    constructor;
    . assumption;
    . suffices REPred fun a : ℕ ↦ T ⊬. φ/[a] by simpa [hA] using this;

      have : 𝚺₁-Predicate fun b : ℕ ↦ T.Provable (neg ℒₒᵣ <| substs ℒₒᵣ ?[InternalArithmetic.numeral b] ⌜φ⌝) := by clear hA; definability;
      apply REPred.of_eq (re_iff_sigma1.mpr this);

      intro a;
      push_neg at h;
      replace h : T ⊢!. ∼φ/[a] ↔ ¬T ⊢!. φ/[a] := by simpa [hA] using h a |>.symm;
      apply Iff.trans ?_ h;

      constructor;
      . rintro hP;
        sorry;
      . rintro hφ;
        have : Theory.Provable T ⌜∼φ/[a]⌝ := provable_of_provable_arith₀ (V := ℕ) hφ;
        sorry;

  push_neg at hd;
  rcases hd with (⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩);
  . use d;
    constructor;
    . simpa [hA] using hd₁;
    . simpa;
  . exfalso;
    apply Entailment.Consistent.not_bot (𝓢 := T.toAxiom) inferInstance;
    simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, Decidable.not_not] at hd₁;
    cl_prover [hd₁, hd₂];

open LO.Entailment in
@[inherit_doc incomplete_of_REPred_not_ComputablePred']
lemma incomplete_of_REPred_not_ComputablePred {A : Set ℕ} (hRE : REPred A) (hC : ¬ComputablePred A) :
  ¬Entailment.Complete (T : Axiom ℒₒᵣ) := by
  obtain ⟨φ, a, hφ₁, hφ₂⟩ := incomplete_of_REPred_not_ComputablePred' (T := T) hRE hC;
  apply incomplete_iff_exists_undecidable.mpr;
  use φ/[⌜a⌝];
  constructor <;> assumption;

end LO.FirstOrder.Arithmetic
