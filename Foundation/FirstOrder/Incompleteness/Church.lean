import Foundation.FirstOrder.Incompleteness.First
import Mathlib.Computability.Reduce

/-!
  # Church's Undecidability of First-Order Logic Theorem
-/

section

lemma Iff.of_not_not {p q : Prop} (hp : ¬p) (hq : ¬q) : p ↔ q := by {
  exact (iff_false_right hq).mpr hp
 }

end

section

lemma Part.cases (p : Part α) : p = Part.none ∨ ∃ a, a ∈ p := by
  by_cases h : p.Dom
  · right; exact Part.dom_iff_mem.mp h
  · left; exact Part.eq_none_iff'.mpr h

variable {α β γ σ} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

lemma ComputablePred.range_subset  {f : α → β} (hf : Computable f) {A} (hA : ComputablePred A) : ComputablePred { x | A (f x) } := by
  apply computable_iff.mpr;
  obtain ⟨inA, hinA₁, rfl⟩ := computable_iff.mp hA;
  use λ x => inA (f x);
  constructor;
  . apply Computable.comp <;> assumption;
  . rfl;

open Computable

lemma Computable.of₁ {f : α → γ} (hf : Computable f) : Computable₂ fun (a : α) (_ : β) ↦ f a := Computable.to₂ (hf.comp fst)

lemma Computable.of₂ {f : β → γ} (hf : Computable f) : Computable₂ fun (_ : α) (b : β) ↦ f b := Computable.to₂ (hf.comp snd)

lemma Partrec.of₁ {f : α →. γ} (hf : Partrec f) : Partrec₂ fun (a : α) (_ : β) ↦ f a := Partrec.to₂ (hf.comp Computable.fst)

lemma Partrec.of₂ {f : β →. γ} (hf : Partrec f) : Partrec₂ fun (_ : α) (b : β) ↦ f b := Partrec.to₂ (hf.comp Computable.snd)

theorem Partrec.optionCasesOn {o : α → Option β} {f : α →. σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a ↦ Option.casesOn (o a) (f a) (g a) := by
  let optToSum : Option β → Unit ⊕ β := fun o ↦ Option.casesOn o (Sum.inl ()) Sum.inr
  have hOptToSum : Computable optToSum :=
    Computable.option_casesOn Computable.id (Computable.const (Sum.inl ())) (Computable.of₂ Computable.sumInr)
  exact (Partrec.sumCasesOn (hOptToSum.comp ho) (Partrec.of₁ hf) hg).of_eq <| by
    intro a
    rcases o a <;> simp [optToSum]

theorem Partrec.rfindOpt_unique {α} {f : ℕ → Option α}
    (H : ∀ {a n}, a ∈ f n → ∀ {b m}, b ∈ f m → a = b) {a} :
    a ∈ Nat.rfindOpt f ↔ ∃ n, a ∈ f n := by
  constructor
  · exact Nat.rfindOpt_spec
  · rintro ⟨n, h⟩
    have h' := Nat.rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec ⟨h', rfl⟩
    rcases H h hk
    exact Part.get_mem h'

lemma ComputablePred.eq {f g : α → β}
    (hf : Computable f) (hg : Computable g) : ComputablePred fun a : α ↦ f a = g a := by
  have : DecidableEq β := Encodable.decidableEqOfEncodable β
  apply ComputablePred.computable_iff.mpr ⟨fun a ↦ f a = g a, ?_, ?_⟩
  · exact (Primrec.eq (α := β)).to_comp.comp hf hg
  · ext a; simp

lemma ComputablePred.ne {f g : α → β}
    (hf : Computable f) (hg : Computable g) : ComputablePred fun a : α ↦ f a ≠ g a :=
  (ComputablePred.eq hf hg).not

private lemma REPred.toComputable_func {f : α → β} (h : REPred fun p : α × β ↦ f p.1 = p.2) :
    ComputablePred fun p : α × β ↦ f p.1 = p.2 := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr ⟨h, ?_⟩
  have : REPred fun p : (α × β) × β ↦ f p.1.1 = p.2 ∧ p.2 ≠ p.1.2 :=
    REPred.and
      (h.comp (α := (α × β) × β) ((fst.comp fst).pair snd))
      (ComputablePred.ne snd (snd.comp fst)).to_re
  exact this.projection.of_eq <| by
    rintro ⟨a, b⟩
    simp

lemma REPred.toComputable {f : α → β} (h : REPred fun p : α × β ↦ f p.1 = p.2) : Computable f := by
  have h : ComputablePred fun p : α × β ↦ f p.1 = p.2 := REPred.toComputable_func h
  rcases ComputablePred.computable_iff.mp h with ⟨c, hc, ec⟩
  replace ec : ∀ p : α × β, c p = true ↔ f p.1 = p.2 := fun p ↦ by symm; simpa using congr_fun ec p
  let g : α → ℕ → Option β := fun a n ↦ (Encodable.decode n : Option β).bind fun b ↦ bif c ⟨a, b⟩ then .some b else .none
  have hg : Computable₂ g := by
    have : Computable₂ fun (p : α × ℕ) (b : β) ↦ bif c ⟨p.1, b⟩ then some b else none :=
      (cond (hc.comp (pair (fst.comp fst) snd))
        (option_some.comp snd) (const none)).to₂ (α := α × ℕ) (β := β)
    exact (Computable.option_bind (Computable.comp Computable.decode Computable.snd) this).to₂
  have := Partrec.rfindOpt hg
  exact this.of_eq <| by
    intro a
    refine Part.eq_some_iff.mpr ?_
    refine (Partrec.rfindOpt_unique ?_).mpr ?_
    · unfold g
      intro b₁ n₁
      rcases (Encodable.decode n₁ : Option β) with (_ | v₁)
      · simp
      intro h₁ b₂ n₂
      rcases (Encodable.decode n₂ : Option β) with (_ | v₂)
      · simp
      revert h₁
      suffices f a = v₁ → v₁ = b₁ → f a = v₂ → v₂ = b₂ → b₁ = b₂ by simpa [Bool.cond_eq_if, ec]
      grind
    · use Encodable.encode (f a)
      simp [g, ec, Bool.cond_eq_if]

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

/-
open LO.Entailment FirstOrder Arithmetic R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

private lemma theory_provability_undecidable : ¬ComputablePred fun n : ℕ ↦ ∃ σ : Sentence ℒₒᵣ, n = ⌜σ⌝ ∧ T ⊢!. σ := by {
  intro hC
  let U : ℕ → Prop := fun n : ℕ ↦ ∀ σ : Sentence ℒₒᵣ, n = ⌜σ⌝ → T ⊬. σ
  have U_re : REPred U := by simpa using hC.not.to_re
  let υ : Semisentence ℒₒᵣ 1 := codeOfREPred U
  have hυ : ∀ n : ℕ, U n ↔ T ⊢!. υ/[↑n] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁, Axiom.provable_iff] using re_complete U_re
  let δ : Semisentence ℒₒᵣ 1 := “σ. ∃ τ, !ssnum τ σ σ ∧ ”
 }
-/

end Arithmetic

end LO.FirstOrder
