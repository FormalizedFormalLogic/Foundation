import Foundation.FirstOrder.Incompleteness.First


section

variable {α : Type*}

/-
  https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ComputablePred.20from.20Nat.20to.20.CE.B1/near/533574370

  Thanks: Robin Arenz: @Rob23oba
-/
section

@[congr]
lemma Part.assert_congr {p₁ p₂ : Prop} {f₁ : p₁ → Part α} {f₂ : p₂ → Part α}
    (hp : p₁ = p₂) (hf : ∀ h, f₁ (hp.mpr_prop h) = f₂ h) :
    Part.assert p₁ f₁ = Part.assert p₂ f₂ := by
  cases hp
  cases funext hf
  rfl

@[simp] lemma Part.assert_false (f : False → Part α) : Part.assert False f = Part.none := by simp [assert_neg]

@[simp] lemma Part.assert_true (f : True → Part α) : Part.assert True f = f trivial := by simp [assert_pos]

lemma REPred.iff_decoded_pred {A : α → Prop} [Primcodable α] :
    REPred A ↔ REPred fun n : ℕ ↦ ∃ a, Encodable.decode n = some a ∧ A a := by
  simp only [REPred, Partrec, Encodable.decode_nat, Part.coe_some, Part.bind_some]
  apply propext_iff.mp;
  congr 1;
  ext n;
  cases (Encodable.decode n : Option α) <;> simp

end


section

lemma ComputablePred.iff_decoded_pred {A : α → Prop} [Primcodable α] :
  ComputablePred A ↔ ComputablePred fun n : ℕ ↦ ∃ a, Encodable.decode n = some a ∧ A a := by
  sorry;

end

end



namespace LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

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
lemma incomplete_of_REPred_not_ComputablePred_Nat
    {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) : Entailment.Incomplete (T : Axiom ℒₒᵣ) := by
  obtain ⟨φ, a, hφ₁, hφ₂⟩ := incomplete_of_REPred_not_ComputablePred_Nat' T hRE hC;
  apply incomplete_def.mpr;
  use φ/[⌜a⌝];
  constructor <;> assumption;

/--
  Halting problem is r.e. but not recursive, so Gödel's first incompleteness theorem follows.
-/
lemma incomplete_of_REPred_not_ComputablePred {P : α → Prop} [h : Primcodable α] (hRE : REPred P) (hC : ¬ComputablePred P) : ¬Entailment.Complete (T : Axiom ℒₒᵣ) := by
  apply incomplete_of_REPred_not_ComputablePred_Nat T (P := λ n : ℕ ↦ ∃ a, Encodable.decode n = some a ∧ P a);
  . apply REPred.iff_decoded_pred.mp hRE;
  . apply ComputablePred.iff_decoded_pred.not.mp hC;

theorem incomplete_of_halting_problem : ¬Entailment.Complete (T : Axiom ℒₒᵣ) := incomplete_of_REPred_not_ComputablePred T
  (ComputablePred.halting_problem_re 0)
  (ComputablePred.halting_problem _)

end LO.FirstOrder.Arithmetic
