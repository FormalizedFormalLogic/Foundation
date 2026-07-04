module

public import Foundation.FirstOrder.Incompleteness.First

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

open LO.Entailment

open Classical

lemma incomplete_of_REPred_not_ComputablePred_Nat' {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) :
  ∃ φ : ArithmeticSemisentence 1, ∃ a : ℕ, T ⊬ φ/[a] ∧ T ⊬ ∼φ/[a] := by
  let φ := codeOfREPred P;
  use φ;
  have hP : P = { n : ℕ | T ⊢ φ/[n] } := Set.ext fun x ↦ re_complete hRE;
  have ⟨d, hd⟩ : ∃ d : ℕ, ¬(¬P d ↔ T ⊢ ∼φ/[d]) := by
    by_contra h;
    apply hC;
    apply ComputablePred.computable_iff_re_compl_re.mpr;
    constructor;
    . assumption;
    . suffices REPred fun a : ℕ ↦ T ⊬ φ/[a] by simpa [hP] using! this;
      have : 𝚺₁-Predicate fun b : ℕ ↦ Bootstrapping.Provable T (Bootstrapping.neg ℒₒᵣ <| Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral b] ⌜φ⌝) := by clear hP; definability;
      apply REPred.of_eq (re_iff_sigma1.mpr this);
      intro a;
      push Not at h;
      apply Iff.trans ?_ $ show T ⊢ ∼φ/[a] ↔ ¬T ⊢ φ/[a] by simpa [hP] using! h a |>.symm;
      constructor;
      . rintro hP
        apply Bootstrapping.Provable.sound
        simpa [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁] using hP;
      . rintro hφ
        simpa [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁] using
          Bootstrapping.internalize_provability (V := ℕ) hφ;
  push Not at hd;
  rcases hd with (⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩);
  . use d;
    constructor;
    . simpa [hP] using! hd₁;
    . simpa;
  . exfalso;
    apply Entailment.Consistent.not_bot (𝓢 := T) inferInstance;
    replace hd₁ : T ⊢ φ/[d] := by simpa [hP] using! hd₁;
    cl_prover [hd₁, hd₂];

/--
  If r.e. but not recursive predicate `P` on `ℕ` exists, then implies incompleteness.
-/
lemma incomplete_of_REPred_not_ComputablePred_Nat
    {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) : Entailment.Incomplete T := by
  obtain ⟨φ, a, hφ₁, hφ₂⟩ := incomplete_of_REPred_not_ComputablePred_Nat' T hRE hC;
  apply incomplete_def.mpr;
  use φ/[⌜a⌝];
  constructor <;> assumption;

/--
  Recursive enumerability of a predicate on a `Primcodable` type is equivalent to
  the recursive enumerability of the corresponding predicate on `ℕ` obtained by decoding.
-/
lemma _root_.REPred.iff_decoded_pred {α : Type*} [Primcodable α] {A : α → Prop} :
    REPred A ↔ REPred fun n : ℕ ↦ (Encodable.decode (α := α) n).elim False A := by
  constructor
  · intro hA
    have hbind : Partrec fun n : ℕ =>
        (Encodable.decode (α := α) n : Part α).bind
          fun a => Part.assert (A a) fun _ => Part.some () :=
      (Computable.ofOption Computable.decode).bind (hA.comp Computable.snd).to₂
    refine (Partrec.dom_re hbind).of_eq fun n => ?_
    rcases h : Encodable.decode (α := α) n with _ | a <;> simp [Part.assert]
  · intro hg
    refine REPred.of_eq (p := fun a => (Encodable.decode (α := α) (Encodable.encode a)).elim False A)
      (hg.comp Computable.encode) fun a => ?_
    simp [Encodable.encodek]

/--
  Computability of a predicate on a `Primcodable` type is equivalent to
  the computability of the corresponding predicate on `ℕ` obtained by decoding.
-/
lemma _root_.ComputablePred.iff_decoded_pred {α : Type*} [Primcodable α] {A : α → Prop} :
    ComputablePred A ↔ ComputablePred fun n : ℕ ↦ (Encodable.decode (α := α) n).elim False A := by
  sorry

/--
  If an r.e. but not recursive predicate `P` on a `Primcodable` type exists, then incompleteness follows.
-/
lemma incomplete_of_REPred_not_ComputablePred {α : Type*} [Primcodable α] {P : α → Prop}
    (hRE : REPred P) (hC : ¬ComputablePred P) : Entailment.Incomplete T := by
  apply incomplete_of_REPred_not_ComputablePred_Nat T
    (P := fun n : ℕ ↦ (Encodable.decode (α := α) n).elim False P)
  · exact REPred.iff_decoded_pred.mp hRE
  · exact ComputablePred.iff_decoded_pred.not.mp hC

/--
  The halting problem is r.e. but not recursive, so Gödel's first incompleteness theorem follows.
-/
theorem incomplete_of_halting_problem : Entailment.Incomplete T :=
  incomplete_of_REPred_not_ComputablePred T
    (ComputablePred.halting_problem_re 0)
    (ComputablePred.halting_problem 0)

end LO.FirstOrder.Arithmetic
