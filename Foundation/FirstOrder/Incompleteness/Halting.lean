import Foundation.FirstOrder.Incompleteness.First



namespace LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] [𝐈𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

open LO.Entailment FirstOrder Arithmetic ISigma1 Metamath

open Classical

lemma incomplete_of_REPred_not_ComputablePred_Nat' {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) :
  ∃ φ : ArithmeticSemisentence 1, ∃ a : ℕ, T ⊬. φ/[a] ∧ T ⊬. ∼φ/[a] := by
  let φ := codeOfREPred P;
  use φ;
  have hP : P = { n : ℕ | T ⊢!. φ/[n] } := Set.ext fun x ↦ re_complete hRE;
  have ⟨d, hd⟩ : ∃ d : ℕ, ¬(¬P d ↔ T ⊢!. ∼φ/[d]) := by
    by_contra h;
    apply hC;
    apply ComputablePred.computable_iff_re_compl_re.mpr;
    constructor;
    . assumption;
    . suffices REPred fun a : ℕ ↦ T ⊬. φ/[a] by simpa [hP] using this;
      have : 𝚺₁-Predicate fun b : ℕ ↦ T.Provable (neg ℒₒᵣ <| substs ℒₒᵣ ?[InternalArithmetic.numeral b] ⌜φ⌝) := by clear hP; definability;
      apply REPred.of_eq (re_iff_sigma1.mpr this);
      intro a;
      push_neg at h;
      apply Iff.trans ?_ $ show T ⊢!. ∼φ/[a] ↔ ¬T ⊢!. φ/[a] by simpa [hP] using h a |>.symm;
      apply Iff.trans ?_ $ show T ⊢! ∼(φ : SyntacticSemiformula ℒₒᵣ 1)/[↑a] ↔ T ⊢!. ∼φ/[a] by
        convert Axiom.provable_iff.symm;
        simp [Rewriting.embedding_substs_eq_substs_coe₁];
      constructor;
      . rintro hP; apply Theory.Provable.sound; simpa [Semiformula.quote_def] using hP;
      . rintro hφ; simpa [Semiformula.quote_def] using internalize_provability (V := ℕ) hφ;
  push_neg at hd;
  rcases hd with (⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩);
  . use d;
    constructor;
    . simpa [hP] using hd₁;
    . simpa;
  . exfalso;
    apply Entailment.Consistent.not_bot (𝓢 := T.toAxiom) inferInstance;
    replace hd₁ : T ⊢!. φ/[d] := by simpa [hP] using hd₁;
    cl_prover [hd₁, hd₂];

/--
  If r.e. but not recursive predicate `P` on `ℕ` exists, then implies incompleteness.
-/
lemma incomplete_of_REPred_not_ComputablePred_Nat {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) : ¬Entailment.Complete (T : Axiom ℒₒᵣ) := by
  obtain ⟨φ, a, hφ₁, hφ₂⟩ := incomplete_of_REPred_not_ComputablePred_Nat' T hRE hC;
  apply incomplete_iff_exists_undecidable.mpr;
  use φ/[⌜a⌝];
  constructor <;> assumption;

/-
lemma _root_.REPred.iff_decoded_pred {A : α → Prop} [Primcodable α] : REPred A ↔ REPred λ n : ℕ ↦ match Encodable.decode n with | some a => A a | none => False := by
  sorry;

lemma _root_.ComputablePred.iff_decoded_pred {A : α → Prop} [h : Primcodable α] : ComputablePred A ↔ ComputablePred λ n : ℕ ↦ match Encodable.decode n with | some a => A a | none => False := by
  sorry;

lemma incomplete_of_REPred_not_ComputablePred₂ {P : α → Prop} [h : Primcodable α] (hRE : REPred P) (hC : ¬ComputablePred P) : ¬Entailment.Complete (T : Axiom ℒₒᵣ) := by
  apply incomplete_of_REPred_not_ComputablePred (P := λ n : ℕ ↦ match h.decode n with | some a => P a | none => False);
  . exact REPred.iff_decoded_pred.mp hRE;
  . exact ComputablePred.iff_decoded_pred.not.mp hC;

/--
  Halting problem is r.e. but not recursive, so Gödel's first incompleteness theorem follows.
-/
theorem incomplete_of_halting_problem : ¬Entailment.Complete (T : Axiom ℒₒᵣ) := incomplete_of_REPred_not_ComputablePred₂
  (ComputablePred.halting_problem_re 0)
  (ComputablePred.halting_problem _)
-/

end LO.FirstOrder.Arithmetic
