module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General

/-!
# The Tarski conditions and disquotation over `𝗣𝗔⁻`

The finite theory `tarski` of Tarski conditions for $\Delta_0$ satisfaction, provable in `𝗜𝚺₁`.
In a model of `𝗣𝗔⁻ ∪ tarski`, the partial satisfaction `Reading.PrenexSatisfied Γ s` holds
of the code of a prenex formula with a $\Delta_0$ matrix exactly when the formula holds.

## References

- [HP98, 1.64(5), Theorem I.1.70, Remark I.1.77, Remark I.1.80]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

/-! ## The Tarski conditions -/

namespace Tarski

noncomputable def boundedSatisfiedVerum : ArithmeticSentence :=
  “∀ z e, !qqVerumDef.val z → !boundedSatisfied.val e z”

noncomputable def boundedSatisfiedFalsum : ArithmeticSentence :=
  “∀ z e, !qqFalsumDef.val z → ¬!boundedSatisfied.val e z”

noncomputable def boundedSatisfiedEq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfied.val e z ↔ vt = vu)”

noncomputable def boundedSatisfiedNeq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfied.val e z ↔ vt ≠ vu)”

noncomputable def boundedSatisfiedLt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfied.val e z ↔ vt < vu)”

noncomputable def boundedSatisfiedNlt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfied.val e z ↔ ¬(vt < vu))”

noncomputable def boundedSatisfiedAnd : ArithmeticSentence := “∀ p q z e, !qqAndDef.val z p q →
    (!boundedSatisfied.val e z ↔ !boundedSatisfied.val e p ∧ !boundedSatisfied.val e q)”

noncomputable def boundedSatisfiedOr : ArithmeticSentence :=
  “∀ p q z e, !isBounded.val p → !(isUFormula ℒₒᵣ).val p → !isBounded.val q →
    !(isUFormula ℒₒᵣ).val q → !qqOrDef.val z p q →
    (!boundedSatisfied.val e z ↔ !boundedSatisfied.val e p ∨ !boundedSatisfied.val e q)”

noncomputable def boundedSatisfiedBall : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !isBounded.val q → !(isUFormula ℒₒᵣ).val q →
    !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBallDef.val z u q → !termValGraph.val v e t →
    (!boundedSatisfied.val e z ↔ ∀ x < v, ∀ e', !adjoinDef.val e' x e →
      !boundedSatisfied.val e' q)”

noncomputable def boundedSatisfiedBex : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBexDef.val z u q → !termValGraph.val v e t →
    (!boundedSatisfied.val e z ↔ ∃ x < v, ∃ e', !adjoinDef.val e' x e ∧
      !boundedSatisfied.val e' q)”

noncomputable def termValBvar : ArithmeticSentence :=
  “∀ e z t v, !qqBvarDef.val t z → (!termValGraph.val v e t ↔ !nthDef.val v e z)”

noncomputable def termValZero : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Arithmetic.zero ↔ v = 0”

noncomputable def termValOne : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Arithmetic.one ↔ v = 1”

noncomputable def termValAdd : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Arithmetic.qqAddGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt + vu)”

noncomputable def termValMul : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Arithmetic.qqMulGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt * vu)”

noncomputable def adjoinTotal : ArithmeticSentence := “∀ x v, ∃ e, !adjoinDef.val e x v”

noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

noncomputable def nthAdjoinSucc : ArithmeticSentence := “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

noncomputable def boundedSatisfiedProper : ArithmeticSentence :=
  “∀ z e, !boundedSatisfied.sigma.val e z ↔ !boundedSatisfied.pi.val e z”

end Tarski

open Bootstrapping.Tarski in
noncomputable def tarski : ArithmeticTheory := {
  boundedSatisfiedVerum,
  boundedSatisfiedFalsum,
  boundedSatisfiedEq,
  boundedSatisfiedNeq,
  boundedSatisfiedLt,
  boundedSatisfiedNlt,
  boundedSatisfiedAnd,
  boundedSatisfiedOr,
  boundedSatisfiedBall,
  boundedSatisfiedBex,
  boundedSatisfiedProper,
  termValBvar,
  termValZero,
  termValOne,
  termValAdd,
  termValMul,
  adjoinTotal,
  nthAdjoinZero,
  nthAdjoinSucc,
  lenNil,
  lenAdjoin
}

lemma tarski_finite : tarski.Finite := by simp [tarski]

/-! ## `𝗜𝚺₁` proves the Tarski conditions -/

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Tarski

lemma models_boundedSatisfiedVerum : V↓[ℒₒᵣ] ⊧ boundedSatisfiedVerum := by
  suffices ∀ z e : V, z = ^⊤ → BoundedSatisfied e z by
    simpa [models_iff, boundedSatisfiedVerum] using this;
  rintro _ e rfl;
  exact BoundedSatisfied.verum e;

lemma models_boundedSatisfiedFalsum : V↓[ℒₒᵣ] ⊧ boundedSatisfiedFalsum := by
  suffices ∀ z e : V, z = ^⊥ → ¬BoundedSatisfied e z by
    simpa [models_iff, boundedSatisfiedFalsum] using this;
  rintro _ e rfl;
  exact BoundedSatisfied.falsum e;

lemma models_boundedSatisfiedEq : V↓[ℒₒᵣ] ⊧ boundedSatisfiedEq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^= u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfied e z ↔ vt = vu) by
    simpa [models_iff, boundedSatisfiedEq] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfied.eq_iff ht hu;

lemma models_boundedSatisfiedNeq : V↓[ℒₒᵣ] ⊧ boundedSatisfiedNeq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≠ u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfied e z ↔ vt ≠ vu) by
    simpa [models_iff, boundedSatisfiedNeq] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfied.neq_iff ht hu;

lemma models_boundedSatisfiedLt : V↓[ℒₒᵣ] ⊧ boundedSatisfiedLt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^< u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfied e z ↔ vt < vu) by
    simpa [models_iff, boundedSatisfiedLt] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfied.lt_iff ht hu;

lemma models_boundedSatisfiedNlt : V↓[ℒₒᵣ] ⊧ boundedSatisfiedNlt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≮ u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfied e z ↔ ¬(vt < vu)) by
    simpa [models_iff, boundedSatisfiedNlt] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfied.nlt_iff ht hu;

lemma models_boundedSatisfiedAnd : V↓[ℒₒᵣ] ⊧ boundedSatisfiedAnd := by
  suffices ∀ p q z e : V, z = p ^⋏ q →
    (BoundedSatisfied e z ↔ BoundedSatisfied e p ∧ BoundedSatisfied e q) by
    simpa [models_iff, boundedSatisfiedAnd] using this;
  rintro p q _ e rfl;
  exact BoundedSatisfied.and_iff;

lemma models_boundedSatisfiedOr : V↓[ℒₒᵣ] ⊧ boundedSatisfiedOr := by
  suffices ∀ p q z e : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded q → IsUFormula ℒₒᵣ q →
      z = p ^⋎ q → (BoundedSatisfied e z ↔ BoundedSatisfied e p ∨ BoundedSatisfied e q) by
    simpa [models_iff, boundedSatisfiedOr] using this;
  rintro p q _ e hdp hfp hdq hfq rfl;
  exact BoundedSatisfied.or_iff hdp hfp hdq hfq;

lemma models_boundedSatisfiedBall : V↓[ℒₒᵣ] ⊧ boundedSatisfiedBall := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → IsBounded q → IsUFormula ℒₒᵣ q →
      u = termBShift ℒₒᵣ t → z = qqBall u q → v = termVal e t →
      (BoundedSatisfied e z ↔ ∀ x < v, BoundedSatisfied (x ∷ e) q) by
    simpa [models_iff, boundedSatisfiedBall] using this;
  rintro t _ q _ e _ ht hdq hfq rfl rfl rfl;
  exact BoundedSatisfied.ball_iff ht hdq hfq;

lemma models_boundedSatisfiedBex : V↓[ℒₒᵣ] ⊧ boundedSatisfiedBex := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → u = termBShift ℒₒᵣ t → z = qqBex u q →
      v = termVal e t → (BoundedSatisfied e z ↔ ∃ x < v, BoundedSatisfied (x ∷ e) q) by
    simpa [models_iff, boundedSatisfiedBex] using this;
  rintro t _ q _ e _ ht rfl rfl rfl;
  exact BoundedSatisfied.bex_iff ht;

lemma models_termValBvar : V↓[ℒₒᵣ] ⊧ termValBvar := by
  suffices ∀ e z t v : V, t = ^#z → (v = termVal e t ↔ v = e.[z]) by
    simpa [models_iff, termValBvar] using this;
  rintro e z _ v rfl;
  simp;

lemma models_termValZero : V↓[ℒₒᵣ] ⊧ termValZero := by
  simp [models_iff, termValZero, numeral_eq_natCast];

lemma models_termValOne : V↓[ℒₒᵣ] ⊧ termValOne := by
  simp [models_iff, termValOne, numeral_eq_natCast];

lemma models_termValAdd : V↓[ℒₒᵣ] ⊧ termValAdd := by
  suffices ∀ e t u s vt vu v : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → s = t ^+ u →
      vt = termVal e t → vu = termVal e u → (v = termVal e s ↔ v = vt + vu) by
    simpa [models_iff, termValAdd] using this;
  rintro e t u _ _ _ v ht hu rfl rfl rfl;
  simp [termVal_add ht hu];

lemma models_termValMul : V↓[ℒₒᵣ] ⊧ termValMul := by
  suffices ∀ e t u s vt vu v : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → s = t ^* u →
      vt = termVal e t → vu = termVal e u → (v = termVal e s ↔ v = vt * vu) by
    simpa [models_iff, termValMul] using this;
  rintro e t u _ _ _ v ht hu rfl rfl rfl;
  simp [termVal_mul ht hu];

lemma models_adjoinTotal : V↓[ℒₒᵣ] ⊧ adjoinTotal := by
  simp [models_iff, adjoinTotal];

lemma models_nthAdjoinZero : V↓[ℒₒᵣ] ⊧ nthAdjoinZero := by
  suffices ∀ x v e y : V, e = x ∷ v → (y = e.[0] ↔ y = x) by
    simpa [models_iff, nthAdjoinZero] using this;
  rintro x v _ y rfl;
  simp;

lemma models_nthAdjoinSucc : V↓[ℒₒᵣ] ⊧ nthAdjoinSucc := by
  suffices ∀ x v e i y : V, e = x ∷ v → (y = e.[i + 1] ↔ y = v.[i]) by
    simpa [models_iff, nthAdjoinSucc] using this;
  rintro x v _ i y rfl;
  simp;

lemma models_lenNil : V↓[ℒₒᵣ] ⊧ lenNil := by
  simp [models_iff, lenNil];

lemma models_lenAdjoin : V↓[ℒₒᵣ] ⊧ lenAdjoin := by
  suffices ∀ x v e l : V, e = x ∷ v → (l + 1 = len e ↔ l = len v) by
    simpa [models_iff, lenAdjoin] using this;
  rintro x v _ l rfl;
  simp;

lemma models_boundedSatisfiedProper : V↓[ℒₒᵣ] ⊧ boundedSatisfiedProper := by
  simp [models_iff, boundedSatisfiedProper, BoundedSatisfied.defined.proper.iff];

end Tarski

open Bootstrapping.Tarski in
lemma models_tarski {σ : ArithmeticSentence} (h : σ ∈ tarski) : V↓[ℒₒᵣ] ⊧ σ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
  exacts [models_boundedSatisfiedVerum, models_boundedSatisfiedFalsum,
    models_boundedSatisfiedEq, models_boundedSatisfiedNeq, models_boundedSatisfiedLt,
    models_boundedSatisfiedNlt, models_boundedSatisfiedAnd, models_boundedSatisfiedOr,
    models_boundedSatisfiedBall, models_boundedSatisfiedBex,
    models_boundedSatisfiedProper, models_termValBvar, models_termValZero, models_termValOne,
    models_termValAdd, models_termValMul, models_adjoinTotal, models_nthAdjoinZero,
    models_nthAdjoinSucc, models_lenNil, models_lenAdjoin];

end models

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_tarski : 𝗜𝚺₁ ⊢* tarski :=
  fun {_} hσ ↦ Arithmetic.complete.{0} _ _ fun _ _ _ ↦ models_tarski hσ

/-! ## Readings in models of `𝗣𝗔⁻` -/

namespace Reading

variable {V : Type*} [ORingStructure V]

def BoundedSatisfied (e z : V) : Prop := V ⊧/![e, z] boundedSatisfied.val

def PrenexSatisfied : Polarity → ℕ → V → V → Prop
  | _, 0 => BoundedSatisfied
  | Γ, s + 1 => fun e z ↦ V ⊧/![e, z] (prenexSatisfied' Γ s).val

def Bounded (z : V) : Prop := V ⊧/![z] isBounded.val

def UFormula (z : V) : Prop := V ⊧/![z] (isUFormula ℒₒᵣ).val

def UTerm (t : V) : Prop := V ⊧/![t] (isUTerm ℒₒᵣ).val

def Adjoin (e' x e : V) : Prop := V ⊧/![e', x, e] adjoinDef.val

def Nth (y e i : V) : Prop := V ⊧/![y, e, i] nthDef.val

def Len (l e : V) : Prop := V ⊧/![l, e] lenDef.val

def TermVal (y e t : V) : Prop := V ⊧/![y, e, t] termValGraph.val

end Reading

lemma read_prenexSatisfied_sigma_succ {V : Type*} [ORingStructure V] (s : ℕ) (e p : V) :
    Reading.PrenexSatisfied 𝚺 (s + 1) e p ↔
      ∃ x e', Reading.Adjoin e' x e ∧ Reading.PrenexSatisfied 𝚷 s e' p := by
  cases s <;> simp [Reading.PrenexSatisfied, Reading.BoundedSatisfied, Reading.Adjoin,
    prenexSatisfied', HierarchySymbol.Semiformula.val_sigma];

section readings

open Reading

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hM : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ)

include hM

-- The readings are unfolded only here, to match them against the sentences of `tarski`.
attribute [local simp] models_iff Reading.BoundedSatisfied Reading.PrenexSatisfied
  Reading.Bounded Reading.UFormula Reading.UTerm Reading.Adjoin Reading.Nth Reading.Len
  Reading.TermVal

private lemma models_of_mem (σ : ArithmeticSentence) (hσ : σ ∈ tarski := by simp [tarski]) :
    M↓[ℒₒᵣ] ⊧ σ :=
  hM σ hσ

lemma read_boundedSatisfiedVerum : ∀ z e : M, M ⊧/![z] qqVerumDef.val →
    Reading.BoundedSatisfied e z := by
  simpa [Tarski.boundedSatisfiedVerum] using models_of_mem hM Tarski.boundedSatisfiedVerum;

lemma read_boundedSatisfiedFalsum : ∀ z e : M, M ⊧/![z] qqFalsumDef.val →
    ¬Reading.BoundedSatisfied e z := by
  simpa [Tarski.boundedSatisfiedFalsum] using models_of_mem hM Tarski.boundedSatisfiedFalsum;

lemma read_boundedSatisfiedEq : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqEQDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfied e z ↔ vt = vu) := by
  simpa [Tarski.boundedSatisfiedEq] using models_of_mem hM Tarski.boundedSatisfiedEq;

lemma read_boundedSatisfiedNeq : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqNEQDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfied e z ↔ vt ≠ vu) := by
  simpa [Tarski.boundedSatisfiedNeq] using models_of_mem hM Tarski.boundedSatisfiedNeq;

lemma read_boundedSatisfiedLt : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqLTDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfied e z ↔ vt < vu) := by
  simpa [Tarski.boundedSatisfiedLt] using models_of_mem hM Tarski.boundedSatisfiedLt;

lemma read_boundedSatisfiedNlt : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqNLTDef.val → TermVal vt e t → TermVal vu e u →
    (Reading.BoundedSatisfied e z ↔ ¬(vt < vu)) := by
  simpa [Tarski.boundedSatisfiedNlt] using models_of_mem hM Tarski.boundedSatisfiedNlt;

lemma read_boundedSatisfiedAnd : ∀ p q z e : M, M ⊧/![z, p, q] qqAndDef.val →
    (Reading.BoundedSatisfied e z ↔
      Reading.BoundedSatisfied e p ∧ Reading.BoundedSatisfied e q) := by
  simpa [Tarski.boundedSatisfiedAnd] using models_of_mem hM Tarski.boundedSatisfiedAnd;

lemma read_boundedSatisfiedOr : ∀ p q z e : M, Reading.Bounded p → UFormula p →
    Reading.Bounded q → UFormula q →
    M ⊧/![z, p, q] qqOrDef.val →
      (Reading.BoundedSatisfied e z ↔
        Reading.BoundedSatisfied e p ∨ Reading.BoundedSatisfied e q) := by
  simpa [Tarski.boundedSatisfiedOr] using models_of_mem hM Tarski.boundedSatisfiedOr;

lemma read_boundedSatisfiedBall : ∀ t u q z e v : M, UTerm t → Reading.Bounded q → UFormula q →
    M ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → M ⊧/![z, u, q] qqBallDef.val → TermVal v e t →
    (Reading.BoundedSatisfied e z ↔
      ∀ x < v, ∀ e', Adjoin e' x e → Reading.BoundedSatisfied e' q) := by
  simpa [Tarski.boundedSatisfiedBall] using models_of_mem hM Tarski.boundedSatisfiedBall;

lemma read_boundedSatisfiedBex : ∀ t u q z e v : M, UTerm t →
    M ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → M ⊧/![z, u, q] qqBexDef.val → TermVal v e t →
    (Reading.BoundedSatisfied e z ↔
      ∃ x < v, ∃ e', Adjoin e' x e ∧ Reading.BoundedSatisfied e' q) := by
  simpa [Tarski.boundedSatisfiedBex] using models_of_mem hM Tarski.boundedSatisfiedBex;

lemma read_termValBvar : ∀ e z t v : M, M ⊧/![t, z] qqBvarDef.val →
    (TermVal v e t ↔ Nth v e z) := by
  simpa [Tarski.termValBvar] using models_of_mem hM Tarski.termValBvar;

lemma read_termValZero : ∀ e v : M, TermVal v e ((𝟎 : ℕ) : M) ↔ v = 0 := by
  simpa [Tarski.termValZero, numeral_eq_natCast] using models_of_mem hM Tarski.termValZero;

lemma read_termValOne : ∀ e v : M, TermVal v e ((𝟏 : ℕ) : M) ↔ v = 1 := by
  simpa [Tarski.termValOne, numeral_eq_natCast] using models_of_mem hM Tarski.termValOne;

lemma read_termValAdd : ∀ e t u s vt vu v : M, UTerm t → UTerm u →
    M ⊧/![s, t, u] Arithmetic.qqAddGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt + vu) := by
  simpa [Tarski.termValAdd] using models_of_mem hM Tarski.termValAdd;

lemma read_termValMul : ∀ e t u s vt vu v : M, UTerm t → UTerm u →
    M ⊧/![s, t, u] Arithmetic.qqMulGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt * vu) := by
  simpa [Tarski.termValMul] using models_of_mem hM Tarski.termValMul;

lemma read_adjoinTotal : ∀ x v : M, ∃ e, Adjoin e x v := by
  simpa [Tarski.adjoinTotal] using models_of_mem hM Tarski.adjoinTotal;

lemma read_nthAdjoinZero : ∀ x v e y : M, Adjoin e x v → (Nth y e 0 ↔ y = x) := by
  simpa [Tarski.nthAdjoinZero] using models_of_mem hM Tarski.nthAdjoinZero;

lemma read_nthAdjoinSucc : ∀ x v e i y : M, Adjoin e x v → (Nth y e (i + 1) ↔ Nth y v i) := by
  simpa [Tarski.nthAdjoinSucc] using models_of_mem hM Tarski.nthAdjoinSucc;

lemma read_lenNil : ∀ l : M, Len l 0 ↔ l = 0 := by
  simpa [Tarski.lenNil] using models_of_mem hM Tarski.lenNil;

lemma read_lenAdjoin : ∀ x v e l : M, Adjoin e x v → (Len (l + 1) e ↔ Len l v) := by
  simpa [Tarski.lenAdjoin] using models_of_mem hM Tarski.lenAdjoin;

lemma read_prenexSatisfied_pi_succ (s : ℕ) (e p : M) :
    Reading.PrenexSatisfied 𝚷 (s + 1) e p ↔
      ∀ x e', Adjoin e' x e → Reading.PrenexSatisfied 𝚺 s e' p := by
  have h := models_of_mem hM Tarski.boundedSatisfiedProper;
  cases s <;> simp_all [Tarski.boundedSatisfiedProper, prenexSatisfied',
    HierarchySymbol.Semiformula.val_sigma];

end readings

/-! ## Disquotation in models of `𝗣𝗔⁻ ∪ tarski` -/

section disquotation

open Reading

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hM : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ)

def Reading.Codes {m : ℕ} (v : Fin m → M) (ev : M) : Prop :=
  Len (m : M) ev ∧ ∀ i : Fin m, Nth (v i) ev (i.val : M)

include hM in
lemma codes_nil (v : Fin 0 → M) : Codes v 0 :=
  ⟨by simpa using (read_lenNil hM 0).mpr rfl, fun i ↦ i.elim0⟩

include hM in
lemma codes_cons {m : ℕ} {v : Fin m → M} {ev ev' x : M} (h : Codes v ev)
    (hadj : Adjoin ev' x ev) : Codes (x :> v) ev' :=
  ⟨by simpa using (read_lenAdjoin hM x ev ev' (m : M) hadj).mpr h.1,
    fun i ↦ Fin.cases (by simpa using (read_nthAdjoinZero hM x ev ev' x hadj).mpr rfl)
      (fun j ↦ by
        simpa using (read_nthAdjoinSucc hM x ev ev' (j.val : M) (v j) hadj).mpr (h.2 j)) i⟩

include hM in
lemma exists_codes : ∀ {m : ℕ} (v : Fin m → M), ∃ ev, Codes v ev := by
  intro m;
  induction m with
  | zero => exact fun v ↦ ⟨0, codes_nil hM v⟩;
  | succ m ih =>
    intro v;
    obtain ⟨ev, hev⟩ := ih (fun i ↦ v i.succ);
    obtain ⟨ev', hadj⟩ := read_adjoinTotal hM (v 0) ev;
    exact ⟨ev', Matrix.cons_head_tail v ▸ codes_cons hM hev hadj⟩;

private lemma uTerm_quote_cast {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) :
    UTerm ((⌜t⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ (isUTerm ℒₒᵣ) (by simp)

private lemma uFormula_quote_cast {k : ℕ} (φ : ArithmeticSemisentence k) :
    UFormula ((⌜φ⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ (isUFormula ℒₒᵣ) (by simp)

private lemma bounded_quote_cast {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ℬ[<, ℒₒᵣ].Closure φ) : Reading.Bounded ((⌜φ⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ isBounded (by simpa using (isBounded_quote_iff (V := ℕ) φ).mpr h)

include hM in
private lemma termVal_quote_cast {k : ℕ} {v : Fin k → M} {ev : M} (hev : Codes v ev)
    (t : ClosedSemiterm ℒₒᵣ k) : TermVal (t.valb v) ev ((⌜t⌝ : ℕ) : M) := by
  induction t with
  | bvar i =>
    have hb : M ⊧/![((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M), ((i.val : ℕ) : M)] qqBvarDef.val :=
      sigmaZero_upward_absolute₂ qqBvarDef (by simp);
    simpa using (read_termValBvar hM ev _ _ (v i) hb).mpr (hev.2 i);
  | fvar x => exact x.elim;
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      rw [show (⌜(FirstOrder.Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝
        : ℕ) = 𝟎 from (Arithmetic.coe_zero_eq (V := ℕ)).symm];
      exact (read_termValZero hM ev 0).mpr rfl;
    | 0, .one, w, _ =>
      rw [show (⌜(FirstOrder.Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝
        : ℕ) = 𝟏 from (Arithmetic.coe_one_eq (V := ℕ)).symm];
      exact (read_termValOne hM ev 1).mpr rfl;
    | 2, .add, w, ih =>
      have hq : M ⊧/![((⌜FirstOrder.Semiterm.func Language.ORing.Func.add w⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        sigmaOne_upward_absolute₃ _ <| (Arithmetic.qqAdd_defined.df _).mpr rfl;
      exact (read_termValAdd hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;
    | 2, .mul, w, ih =>
      have hq : M ⊧/![((⌜FirstOrder.Semiterm.func Language.ORing.Func.mul w⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        sigmaOne_upward_absolute₃ _ <| (Arithmetic.qqMul_defined.df _).mpr rfl;
      exact (read_termValMul hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;

include hM in
private lemma boundedSatisfied_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.BoundedSatisfied ev ((⌜φ⌝ : ℕ) : M) ↔ M ⊧/v φ) := by
  revert hφ;
  apply Bounding.Closure.arithmetic_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.BoundedSatisfied ev ((⌜φ⌝ : ℕ) : M) ↔ M ⊧/v φ));
  · intro m v ev _;
    exact iff_of_true (read_boundedSatisfiedVerum hM _ ev
      (sigmaZero_upward_absolute₁ qqVerumDef (by simp [Sentence.quote_verum]))) (by simp);
  · intro m v ev _;
    exact iff_of_false (read_boundedSatisfiedFalsum hM _ ev
      (sigmaZero_upward_absolute₁ qqFalsumDef (by simp [Sentence.quote_falsum]))) (by simp);
  · intro m t u v ev hev;
    exact (read_boundedSatisfiedEq hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqEQDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_rel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfiedNeq hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqNEQDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_nrel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfiedLt hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqLTDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_rel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfiedNlt hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqNLTDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_nrel]);
  · intro m φ ψ _ _ ihφ ihψ v ev hev;
    exact (read_boundedSatisfiedAnd hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev
      (sigmaZero_upward_absolute₃ qqAndDef (by simp))).trans (by simp [ihφ v ev hev, ihψ v ev hev]);
  · intro m φ ψ hφ hψ ihφ ihψ v ev hev;
    exact (read_boundedSatisfiedOr hM _ _ _ ev (bounded_quote_cast hφ) (uFormula_quote_cast φ)
      (bounded_quote_cast hψ) (uFormula_quote_cast ψ)
      (sigmaZero_upward_absolute₃ qqOrDef (by simp))).trans (by simp [ihφ v ev hev, ihψ v ev hev]);
  · intro m t φ hφ ihφ v ev hev;
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := sigmaOne_upward_absolute₂ (termBShiftGraph ℒₒᵣ) (by simp);
    have hq : M ⊧/![((⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBallDef.val :=
      sigmaOne_upward_absolute₃ qqBallDef (by simpa using quote_ball_sentence (V := ℕ) t φ);
    rw [read_boundedSatisfiedBall hM _ _ _ _ ev _ (uTerm_quote_cast t) (bounded_quote_cast hφ)
      (uFormula_quote_cast φ) hu hq (termVal_quote_cast hM hev t)];
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel];
    constructor;
    · intro h x hx;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp
        (h x (by simpa [Function.comp_def] using hx) e' hadj);
    · intro h x hx e' hadj;
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr
        (by simpa [Function.comp_def] using h x (by simpa [Function.comp_def] using hx));
  · intro m t φ hφ ihφ v ev hev;
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := sigmaOne_upward_absolute₂ (termBShiftGraph ℒₒᵣ) (by simp);
    have hq : M ⊧/![((⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBexDef.val :=
      sigmaOne_upward_absolute₃ qqBexDef (by simpa using quote_bex_sentence (V := ℕ) t φ);
    rw [read_boundedSatisfiedBex hM _ _ _ _ ev _ (uTerm_quote_cast t) hu hq
      (termVal_quote_cast hM hev t)];
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel];
    constructor;
    · rintro ⟨x, hx, e', hadj, hsat⟩;
      exact ⟨x, by simpa [Function.comp_def] using hx,
        (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩;
    · rintro ⟨x, hx, hsat⟩;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact ⟨x, by simpa [Function.comp_def] using hx, e', hadj,
        (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr (by simpa [Function.comp_def] using hsat)⟩;

include hM in
lemma prenexSatisfied_quote_reading : ∀ {Γ : Polarity} {s k : ℕ}
    {θ : ArithmeticSemisentence (k + s)}, ℬ[<, ℒₒᵣ].Closure θ →
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.PrenexSatisfied Γ s ev ((⌜θ⌝ : ℕ) : M) ↔ M ⊧/v (θ.toPrenex Γ s))
  | _, 0, _, _, hθ, v, ev, hev => boundedSatisfied_quote_reading hM hθ v ev hev
  | 𝚺, s + 1, k, θ, hθ, v, ev, hev => by
    have ih := prenexSatisfied_quote_reading (Γ := 𝚷)
      (closure_cast (Nat.succ_add k s).symm hθ);
    rw [read_prenexSatisfied_sigma_succ, quote_cast (Nat.succ_add k s).symm] at *;
    simp only [Polarity.quantItr_succ, Polarity.quant_sigma, Semiformula.eval_ex];
    constructor;
    · rintro ⟨x, e', hadj, hsat⟩;
      exact ⟨x, (ih (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩;
    · rintro ⟨x, hsat⟩;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact ⟨x, e', hadj, (ih (x :> v) e' (codes_cons hM hev hadj)).mpr hsat⟩;
  | 𝚷, s + 1, k, θ, hθ, v, ev, hev => by
    have ih := prenexSatisfied_quote_reading (Γ := 𝚺)
      (closure_cast (Nat.succ_add k s).symm hθ);
    rw [read_prenexSatisfied_pi_succ hM, quote_cast (Nat.succ_add k s).symm] at *;
    simp only [Polarity.quantItr_succ, Polarity.quant_pi, Semiformula.eval_all];
    constructor;
    · intro hsat x;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact (ih (x :> v) e' (codes_cons hM hev hadj)).mp (hsat x e' hadj);
    · intro hsat x e' hadj;
      exact (ih (x :> v) e' (codes_cons hM hev hadj)).mpr (hsat x);

end disquotation

end FFL.FirstOrder.Arithmetic.Bootstrapping
