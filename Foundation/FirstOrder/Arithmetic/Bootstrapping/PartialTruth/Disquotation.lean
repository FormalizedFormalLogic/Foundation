module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.HierarchicalSatisfaction

/-!
# The Tarski conditions and disquotation over `𝗣𝗔⁻`

The Tarski conditions for $\Delta_0$ satisfaction as explicit arithmetic sentences, together with
the agreement of its $\Sigma_1$ and $\Pi_1$ definitions, collected into the finite theory
`tarski`, which `𝗜𝚺₁` proves. Reading these sentences and the defining formulas of
`HierarchicalSatisfaction` inside a model of `𝗣𝗔⁻ ∪ tarski` yields, uniformly in the level, the
disquotation lemma `𝗣𝗔⁻ ∪ tarski ⊢ disquotation φ` for prenex formulas `φ` with a $\Delta_0$
matrix and free variables.

## References

- [HP98, 1.64(5), Theorem I.1.70, Remark I.1.77, Remark I.1.80]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

/-! ## The Tarski conditions -/


namespace Tarski

noncomputable def boundedSatisfactionVerum : ArithmeticSentence :=
  “∀ z e, !qqVerumDef.val z → !boundedSatisfaction.val z e”

noncomputable def boundedSatisfactionFalsum : ArithmeticSentence :=
  “∀ z e, !qqFalsumDef.val z → ¬!boundedSatisfaction.val z e”

noncomputable def boundedSatisfactionEq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfaction.val z e ↔ vt = vu)”

noncomputable def boundedSatisfactionNeq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfaction.val z e ↔ vt ≠ vu)”

noncomputable def boundedSatisfactionLt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfaction.val z e ↔ vt < vu)”

noncomputable def boundedSatisfactionNlt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!boundedSatisfaction.val z e ↔ ¬(vt < vu))”

noncomputable def boundedSatisfactionAnd : ArithmeticSentence := “∀ p q z e, !qqAndDef.val z p q →
    (!boundedSatisfaction.val z e ↔ !boundedSatisfaction.val p e ∧ !boundedSatisfaction.val q e)”

noncomputable def boundedSatisfactionOr : ArithmeticSentence :=
  “∀ p q z e, !isBounded.val p → !(isUFormula ℒₒᵣ).val p → !isBounded.val q →
    !(isUFormula ℒₒᵣ).val q → !qqOrDef.val z p q →
    (!boundedSatisfaction.val z e ↔ !boundedSatisfaction.val p e ∨ !boundedSatisfaction.val q e)”
noncomputable def boundedSatisfactionBall : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !isBounded.val q → !(isUFormula ℒₒᵣ).val q →
    !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBallDef.val z u q → !termValGraph.val v e t →
    (!boundedSatisfaction.val z e ↔ ∀ x < v, ∀ e', !adjoinDef.val e' x e →
      !boundedSatisfaction.val q e')”

noncomputable def boundedSatisfactionBex : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBexDef.val z u q → !termValGraph.val v e t →
    (!boundedSatisfaction.val z e ↔ ∃ x < v, ∃ e', !adjoinDef.val e' x e ∧
      !boundedSatisfaction.val q e')”

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

noncomputable def boundedSatisfactionProper : ArithmeticSentence :=
  “∀ z e, !boundedSatisfaction.sigma.val z e ↔ !boundedSatisfaction.pi.val z e”

end Tarski

open Bootstrapping.Tarski in
noncomputable def tarski : ArithmeticTheory := {
  boundedSatisfactionVerum,
  boundedSatisfactionFalsum,
  boundedSatisfactionEq,
  boundedSatisfactionNeq,
  boundedSatisfactionLt,
  boundedSatisfactionNlt,
  boundedSatisfactionAnd,
  boundedSatisfactionOr,
  boundedSatisfactionBall,
  boundedSatisfactionBex,
  boundedSatisfactionProper,
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

section

open Bootstrapping.Tarski

-- Each Tarski sentence is a universal closure of a Boolean combination of formulas of level at
-- most `𝚺 2`: `iff_iff` splits the biconditionals, and `dummy_sigma`, `dummy_pi` absorb the
-- quantifier blocks that raise the level by one.
attribute [local simp] Bounding.Hierarchy.iff_iff Bounding.Hierarchy.dummy_sigma
  Bounding.Hierarchy.dummy_pi HierarchySymbol.Semiformula.hierarchy_of_lt

lemma hierarchy_of_tarski {σ : ArithmeticSentence} (hσ : σ ∈ tarski) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 3 σ := by
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boundedSatisfactionVerum, boundedSatisfactionFalsum, boundedSatisfactionEq,
      boundedSatisfactionNeq, boundedSatisfactionLt, boundedSatisfactionNlt,
      boundedSatisfactionAnd, boundedSatisfactionOr, boundedSatisfactionBall,
      boundedSatisfactionBex, boundedSatisfactionProper, termValBvar, termValZero, termValOne,
      termValAdd, termValMul, adjoinTotal, nthAdjoinZero, nthAdjoinSucc, lenNil, lenAdjoin];

end

/-! ## `𝗜𝚺₁` proves the Tarski conditions -/

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Tarski

lemma models_boundedSatisfactionVerum : V↓[ℒₒᵣ] ⊧ boundedSatisfactionVerum := by
  suffices ∀ z e : V, z = ^⊤ → BoundedSatisfaction z e by
    simpa [models_iff, boundedSatisfactionVerum] using this;
  rintro _ e rfl;
  exact BoundedSatisfaction.verum e;

lemma models_boundedSatisfactionFalsum : V↓[ℒₒᵣ] ⊧ boundedSatisfactionFalsum := by
  suffices ∀ z e : V, z = ^⊥ → ¬BoundedSatisfaction z e by
    simpa [models_iff, boundedSatisfactionFalsum] using this;
  rintro _ e rfl;
  exact BoundedSatisfaction.falsum e;

lemma models_boundedSatisfactionEq : V↓[ℒₒᵣ] ⊧ boundedSatisfactionEq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^= u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfaction z e ↔ vt = vu) by
    simpa [models_iff, boundedSatisfactionEq] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfaction.eq_iff ht hu;

lemma models_boundedSatisfactionNeq : V↓[ℒₒᵣ] ⊧ boundedSatisfactionNeq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≠ u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfaction z e ↔ vt ≠ vu) by
    simpa [models_iff, boundedSatisfactionNeq] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfaction.neq_iff ht hu;

lemma models_boundedSatisfactionLt : V↓[ℒₒᵣ] ⊧ boundedSatisfactionLt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^< u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfaction z e ↔ vt < vu) by
    simpa [models_iff, boundedSatisfactionLt] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfaction.lt_iff ht hu;

lemma models_boundedSatisfactionNlt : V↓[ℒₒᵣ] ⊧ boundedSatisfactionNlt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≮ u →
      vt = termVal e t → vu = termVal e u → (BoundedSatisfaction z e ↔ ¬(vt < vu)) by
    simpa [models_iff, boundedSatisfactionNlt] using this;
  rintro t u _ e _ _ ht hu rfl rfl rfl;
  exact BoundedSatisfaction.nlt_iff ht hu;

lemma models_boundedSatisfactionAnd : V↓[ℒₒᵣ] ⊧ boundedSatisfactionAnd := by
  suffices ∀ p q z e : V, z = p ^⋏ q →
    (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e) by
    simpa [models_iff, boundedSatisfactionAnd] using this;
  rintro p q _ e rfl;
  exact BoundedSatisfaction.and_iff;

lemma models_boundedSatisfactionOr : V↓[ℒₒᵣ] ⊧ boundedSatisfactionOr := by
  suffices ∀ p q z e : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded q → IsUFormula ℒₒᵣ q →
      z = p ^⋎ q → (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e) by
    simpa [models_iff, boundedSatisfactionOr] using this;
  rintro p q _ e hdp hfp hdq hfq rfl;
  exact BoundedSatisfaction.or_iff hdp hfp hdq hfq;

lemma models_boundedSatisfactionBall : V↓[ℒₒᵣ] ⊧ boundedSatisfactionBall := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → IsBounded q → IsUFormula ℒₒᵣ q →
      u = termBShift ℒₒᵣ t → z = qqBall u q → v = termVal e t →
      (BoundedSatisfaction z e ↔ ∀ x < v, BoundedSatisfaction q (x ∷ e)) by
    simpa [models_iff, boundedSatisfactionBall] using this;
  rintro t _ q _ e _ ht hdq hfq rfl rfl rfl;
  exact BoundedSatisfaction.ball_iff ht hdq hfq;

lemma models_boundedSatisfactionBex : V↓[ℒₒᵣ] ⊧ boundedSatisfactionBex := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → u = termBShift ℒₒᵣ t → z = qqBex u q →
      v = termVal e t → (BoundedSatisfaction z e ↔ ∃ x < v, BoundedSatisfaction q (x ∷ e)) by
    simpa [models_iff, boundedSatisfactionBex] using this;
  rintro t _ q _ e _ ht rfl rfl rfl;
  exact BoundedSatisfaction.bex_iff ht;

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

lemma models_boundedSatisfactionProper : V↓[ℒₒᵣ] ⊧ boundedSatisfactionProper := by
  simp [models_iff, boundedSatisfactionProper, BoundedSatisfaction.defined.proper.iff];

end Tarski

open Bootstrapping.Tarski in
lemma models_tarski {σ : ArithmeticSentence} (h : σ ∈ tarski) : V↓[ℒₒᵣ] ⊧ σ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
  exacts [models_boundedSatisfactionVerum, models_boundedSatisfactionFalsum,
    models_boundedSatisfactionEq, models_boundedSatisfactionNeq, models_boundedSatisfactionLt,
    models_boundedSatisfactionNlt, models_boundedSatisfactionAnd, models_boundedSatisfactionOr,
    models_boundedSatisfactionBall, models_boundedSatisfactionBex,
    models_boundedSatisfactionProper, models_termValBvar, models_termValZero, models_termValOne,
    models_termValAdd, models_termValMul, models_adjoinTotal, models_nthAdjoinZero,
    models_nthAdjoinSucc, models_lenNil, models_lenAdjoin];

end models

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_tarski : 𝗜𝚺₁ ⊢* tarski :=
  fun {_} hσ ↦ Arithmetic.complete.{0} _ _ fun _ _ _ ↦ models_tarski hσ

/-! ## Readings in models of `𝗣𝗔⁻` -/

namespace Reading

variable {V : Type*} [ORingStructure V]

def BoundedSatisfaction (z e : V) : Prop := V ⊧/![z, e] boundedSatisfaction.val

def HierarchicalSatisfaction (Γ : Polarity) (s : ℕ) (z e : V) : Prop :=
  V ⊧/![z, e] (hierarchicalSatisfactionDef Γ s)

def Bounded (z : V) : Prop := V ⊧/![z] isBounded.val

def UFormula (z : V) : Prop := V ⊧/![z] (isUFormula ℒₒᵣ).val

def UTerm (t : V) : Prop := V ⊧/![t] (isUTerm ℒₒᵣ).val

def Adjoin (e' x e : V) : Prop := V ⊧/![e', x, e] adjoinDef.val

def Nth (y e i : V) : Prop := V ⊧/![y, e, i] nthDef.val

def Len (l e : V) : Prop := V ⊧/![l, e] lenDef.val

def TermVal (y e t : V) : Prop := V ⊧/![y, e, t] termValGraph.val

end Reading

lemma read_hierarchicalSatisfaction_sigma_succ {V : Type*} [ORingStructure V] (s : ℕ) (p e : V) :
    Reading.HierarchicalSatisfaction 𝚺 (s + 1) p e ↔
      ∃ x e', Reading.Adjoin e' x e ∧ Reading.HierarchicalSatisfaction 𝚷 s p e' := by
  cases s <;> simp [Reading.HierarchicalSatisfaction, Reading.Adjoin, hierarchicalSatisfactionDef,
    hierarchicalSatisfaction, hierarchicalSatisfaction', HierarchySymbol.Semiformula.val_sigma];

/-! ### The Tarski conditions read in a model of `𝗣𝗔⁻ ∪ tarski` -/

section readings

open Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hM : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ)

include hM

-- The readings are unfolded only here, to match them against the sentences of `tarski`.
attribute [local simp] models_iff Reading.BoundedSatisfaction Reading.HierarchicalSatisfaction
  Reading.Bounded Reading.UFormula Reading.UTerm Reading.Adjoin Reading.Nth Reading.Len
  Reading.TermVal

private lemma models_of_mem (σ : ArithmeticSentence) (hσ : σ ∈ tarski := by simp [tarski]) :
    M↓[ℒₒᵣ] ⊧ σ :=
  hM σ hσ

lemma read_boundedSatisfactionVerum : ∀ z e : M, M ⊧/![z] qqVerumDef.val →
    Reading.BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionVerum] using models_of_mem hM Tarski.boundedSatisfactionVerum;

lemma read_boundedSatisfactionFalsum : ∀ z e : M, M ⊧/![z] qqFalsumDef.val →
    ¬Reading.BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionFalsum] using models_of_mem hM Tarski.boundedSatisfactionFalsum;

lemma read_boundedSatisfactionEq : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqEQDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfaction z e ↔ vt = vu) := by
  simpa [Tarski.boundedSatisfactionEq] using models_of_mem hM Tarski.boundedSatisfactionEq;

lemma read_boundedSatisfactionNeq : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqNEQDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfaction z e ↔ vt ≠ vu) := by
  simpa [Tarski.boundedSatisfactionNeq] using models_of_mem hM Tarski.boundedSatisfactionNeq;

lemma read_boundedSatisfactionLt : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqLTDef.val → TermVal vt e t → TermVal vu e u →
      (Reading.BoundedSatisfaction z e ↔ vt < vu) := by
  simpa [Tarski.boundedSatisfactionLt] using models_of_mem hM Tarski.boundedSatisfactionLt;

lemma read_boundedSatisfactionNlt : ∀ t u z e vt vu : M, UTerm t → UTerm u →
    M ⊧/![z, t, u] qqNLTDef.val → TermVal vt e t → TermVal vu e u →
    (Reading.BoundedSatisfaction z e ↔ ¬(vt < vu)) := by
  simpa [Tarski.boundedSatisfactionNlt] using models_of_mem hM Tarski.boundedSatisfactionNlt;

lemma read_boundedSatisfactionAnd : ∀ p q z e : M, M ⊧/![z, p, q] qqAndDef.val →
    (Reading.BoundedSatisfaction z e ↔
      Reading.BoundedSatisfaction p e ∧ Reading.BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionAnd] using models_of_mem hM Tarski.boundedSatisfactionAnd;

lemma read_boundedSatisfactionOr : ∀ p q z e : M, Reading.Bounded p → UFormula p →
    Reading.Bounded q → UFormula q →
    M ⊧/![z, p, q] qqOrDef.val →
      (Reading.BoundedSatisfaction z e ↔
        Reading.BoundedSatisfaction p e ∨ Reading.BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionOr] using models_of_mem hM Tarski.boundedSatisfactionOr;

lemma read_boundedSatisfactionBall : ∀ t u q z e v : M, UTerm t → Reading.Bounded q → UFormula q →
    M ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → M ⊧/![z, u, q] qqBallDef.val → TermVal v e t →
    (Reading.BoundedSatisfaction z e ↔
      ∀ x < v, ∀ e', Adjoin e' x e → Reading.BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBall] using models_of_mem hM Tarski.boundedSatisfactionBall;

lemma read_boundedSatisfactionBex : ∀ t u q z e v : M, UTerm t →
    M ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → M ⊧/![z, u, q] qqBexDef.val → TermVal v e t →
    (Reading.BoundedSatisfaction z e ↔
      ∃ x < v, ∃ e', Adjoin e' x e ∧ Reading.BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBex] using models_of_mem hM Tarski.boundedSatisfactionBex;

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

lemma read_hierarchicalSatisfaction_pi_succ (s : ℕ) (p e : M) :
    Reading.HierarchicalSatisfaction 𝚷 (s + 1) p e ↔
      ∀ x e', Adjoin e' x e → Reading.HierarchicalSatisfaction 𝚺 s p e' := by
  have h := models_of_mem hM Tarski.boundedSatisfactionProper;
  cases s <;> simp_all [Tarski.boundedSatisfactionProper, hierarchicalSatisfactionDef,
    hierarchicalSatisfaction, hierarchicalSatisfaction', HierarchySymbol.Semiformula.val_sigma];

end readings

/-! ## Disquotation over `𝗣𝗔⁻` -/

noncomputable def hierarchicalSatisfactionVec (Γ : Polarity) (s k : ℕ) :
    ArithmeticSemisentence (k + 1) :=
  “p. ∃ e, !lenDef ↑k e ∧ (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(hierarchicalSatisfactionDef Γ s) p e”

noncomputable def disquotation {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k) :
    ArithmeticSentence :=
  ∀¹* (φ.val 🡘 (hierarchicalSatisfactionVec Γ s k) ⇜
    ((⌜φ.matrix.val⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

section disquotation

open _root_.FFL.FirstOrder.Tarski Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hM : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ)

/-! ### Codes of finite sequences -/

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

/-! ### Coding facts about standard codes -/

private lemma uTerm_quote_cast {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) :
    UTerm ((⌜t⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ (isUTerm ℒₒᵣ) (by simp)

private lemma uFormula_quote_cast {k : ℕ} (φ : ArithmeticSemisentence k) :
    UFormula ((⌜φ⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ (isUFormula ℒₒᵣ) (by simp)

private lemma bounded_quote_cast {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ℬ[<, ℒₒᵣ].Closure φ) : Reading.Bounded ((⌜φ⌝ : ℕ) : M) :=
  deltaOne_upward_absolute₁ isBounded (by simpa using (isBounded_quote_iff (V := ℕ) φ).mpr h)

/-! ### Evaluation of coded closed terms -/

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
        : ℕ) = 𝟎 by simp];
      exact (read_termValZero hM ev 0).mpr rfl;
    | 0, .one, w, _ =>
      rw [show (⌜(FirstOrder.Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝
        : ℕ) = 𝟏 by simp];
      exact (read_termValOne hM ev 1).mpr rfl;
    | 2, .add, w, ih =>
      have hq : M ⊧/![((⌜FirstOrder.Semiterm.func Language.ORing.Func.add w⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqAddGraph (by simp);
      exact (read_termValAdd hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;
    | 2, .mul, w, ih =>
      have hq : M ⊧/![((⌜FirstOrder.Semiterm.func Language.ORing.Func.mul w⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqMulGraph (by simp);
      exact (read_termValMul hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;

/-! ### The $\Delta_0$ base case -/

include hM in
private lemma boundedSatisfaction_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  revert hφ;
  apply Bounding.Closure.arithmetic_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ));
  · intro m v ev _;
    exact iff_of_true (read_boundedSatisfactionVerum hM _ ev
      (sigmaZero_upward_absolute₁ qqVerumDef (by simp [Sentence.quote_verum]))) (by simp);
  · intro m v ev _;
    exact iff_of_false (read_boundedSatisfactionFalsum hM _ ev
      (sigmaZero_upward_absolute₁ qqFalsumDef (by simp [Sentence.quote_falsum]))) (by simp);
  · intro m t u v ev hev;
    exact (read_boundedSatisfactionEq hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqEQDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_rel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfactionNeq hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqNEQDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_nrel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfactionLt hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqLTDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_rel]);
  · intro m t u v ev hev;
    exact (read_boundedSatisfactionNlt hM _ _ _ ev _ _ (uTerm_quote_cast t) (uTerm_quote_cast u)
      (sigmaOne_upward_absolute₃ qqNLTDef (by simp)) (termVal_quote_cast hM hev t)
      (termVal_quote_cast hM hev u)).trans (by simp [Semiformula.eval_nrel]);
  · intro m φ ψ _ _ ihφ ihψ v ev hev;
    exact (read_boundedSatisfactionAnd hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev
      (sigmaZero_upward_absolute₃ qqAndDef (by simp))).trans (by simp [ihφ v ev hev, ihψ v ev hev]);
  · intro m φ ψ hφ hψ ihφ ihψ v ev hev;
    exact (read_boundedSatisfactionOr hM _ _ _ ev (bounded_quote_cast hφ) (uFormula_quote_cast φ)
      (bounded_quote_cast hψ) (uFormula_quote_cast ψ)
      (sigmaZero_upward_absolute₃ qqOrDef (by simp))).trans (by simp [ihφ v ev hev, ihψ v ev hev]);
  · intro m t φ hφ ihφ v ev hev;
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := sigmaOne_upward_absolute₂ (termBShiftGraph ℒₒᵣ) (by simp);
    have hq : M ⊧/![((⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBallDef.val :=
      sigmaOne_upward_absolute₃ qqBallDef (by simpa using quote_ball_sentence (V := ℕ) t φ);
    rw [read_boundedSatisfactionBall hM _ _ _ _ ev _ (uTerm_quote_cast t) (bounded_quote_cast hφ)
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
    rw [read_boundedSatisfactionBex hM _ _ _ _ ev _ (uTerm_quote_cast t) hu hq
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

/-! ### The prenex induction -/

include hM in
private lemma hierarchicalSatisfaction_quote_reading : ∀ {Γ : Polarity} {s k : ℕ}
    {θ : ArithmeticSemisentence (k + s)}, ℬ[<, ℒₒᵣ].Closure θ →
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.HierarchicalSatisfaction Γ s ((⌜θ⌝ : ℕ) : M) ev ↔ M ⊧/v (θ.toPrenex Γ s))
  | _, 0, _, _, hθ, v, ev, hev => boundedSatisfaction_quote_reading hM hθ v ev hev
  | 𝚺, s + 1, k, θ, hθ, v, ev, hev => by
    have ih := hierarchicalSatisfaction_quote_reading (Γ := 𝚷)
      (closure_cast (Nat.succ_add k s).symm hθ);
    rw [read_hierarchicalSatisfaction_sigma_succ, quote_cast (Nat.succ_add k s).symm] at *;
    simp only [Polarity.quantItr_succ, Polarity.quant_sigma, Semiformula.eval_ex];
    constructor;
    · rintro ⟨x, e', hadj, hsat⟩;
      exact ⟨x, (ih (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩;
    · rintro ⟨x, hsat⟩;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact ⟨x, e', hadj, (ih (x :> v) e' (codes_cons hM hev hadj)).mpr hsat⟩;
  | 𝚷, s + 1, k, θ, hθ, v, ev, hev => by
    have ih := hierarchicalSatisfaction_quote_reading (Γ := 𝚺)
      (closure_cast (Nat.succ_add k s).symm hθ);
    rw [read_hierarchicalSatisfaction_pi_succ hM, quote_cast (Nat.succ_add k s).symm] at *;
    simp only [Polarity.quantItr_succ, Polarity.quant_pi, Semiformula.eval_all];
    constructor;
    · intro hsat x;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact (ih (x :> v) e' (codes_cons hM hev hadj)).mp (hsat x e' hadj);
    · intro hsat x e' hadj;
      exact (ih (x :> v) e' (codes_cons hM hev hadj)).mpr (hsat x);

/-! ### Assembling the disquotation lemma over `𝗣𝗔⁻` -/

private lemma eval_hierarchicalSatisfactionVec {Γ : Polarity} {s k : ℕ} (p : M) (w : Fin k → M) :
    M ⊧/(p :> w) (hierarchicalSatisfactionVec Γ s k) ↔
      ∃ ev, Codes w ev ∧ Reading.HierarchicalSatisfaction Γ s p ev := by
  simp only [hierarchicalSatisfactionVec, Nat.succ_eq_add_one, Nat.reduceAdd,
    Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app, Semiterm.val_bvar, Matrix.cons_val_zero, Fin.isValue, Fin.Fin1.eq_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃,
    Semiformula.eval_operator, Matrix.cons_val_succ, Tarski.Structure.eq_iff_eq,
    LogicalConnective.Prop.and_eq, exists_eq_right, Reading.Codes, Reading.Len, Reading.Nth,
    Reading.HierarchicalSatisfaction, and_assoc];

private lemma eval_disquotation_rhs {Γ : Polarity} {s k m : ℕ} (φ : ArithmeticSemisentence m)
    (e : Fin k → M) :
    M ⊧/e ((hierarchicalSatisfactionVec Γ s k) ⇜
        ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))
      ↔ M ⊧/(((⌜φ⌝ : ℕ) : M) :> e) (hierarchicalSatisfactionVec Γ s k) := by
  simp only [Semiformula.eval_substs, Matrix.comp_vecCons'', Arithmetic.gödelNumber'_def,
    Semiterm.Operator.encode, Semiterm.Operator.const, Semiterm.val_operator,
    Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app, Sentence.quote_eq_encode_nat,
    Matrix.empty_eq];
  simp only [Function.comp_def, Semiterm.val_bvar];

end disquotation


theorem provable_disquotation_of_tarski {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k) :
    𝗣𝗔⁻ ∪ tarski ⊢ disquotation φ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ ∪ tarski) := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance
      (Entailment.Axiomatized.le_of_subset Set.subset_union_left);
  apply Arithmetic.provable_iff_of_models_iff.{0} (T := 𝗣𝗔⁻ ∪ tarski);
  intro M _ hMT e;
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := Semantics.ModelsSet.of_subset hMT Set.subset_union_left;
  have hM (σ : ArithmeticSentence) (hσ : σ ∈ tarski) : M↓[ℒₒᵣ] ⊧ σ :=
    Semantics.ModelsSet.models _ (Set.mem_union_right 𝗣𝗔⁻ hσ);
  rw [eval_disquotation_rhs, eval_hierarchicalSatisfactionVec];
  obtain ⟨ev₀, hev₀⟩ := exists_codes hM e;
  have H {ev : M} (hev : Reading.Codes e ev) :=
    hierarchicalSatisfaction_quote_reading hM (Γ := Γ) φ.matrix.bounded e ev hev;
  exact ⟨fun h ↦ ⟨ev₀, hev₀, (H hev₀).mpr h⟩, fun ⟨ev, hev, hsat⟩ ↦ (H hev).mp hsat⟩;

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_disquotation {Γ : Polarity} {s k : ℕ}
    (φ : Prenex Γ s Empty k) :
    𝗜𝚺₁ ⊢ disquotation φ := by
  have : 𝗣𝗔⁻ ∪ tarski ⪯ 𝗜𝚺₁ := Entailment.WeakerThan.ofAxm! fun {σ} hσ ↦ by
    rcases hσ with h | h;
    · exact Entailment.WeakerThan.pbl (Entailment.by_axm h);
    · exact ISigma1.provable_tarski h;
  exact this.pbl (provable_disquotation_of_tarski φ);


end FFL.FirstOrder.Arithmetic.Bootstrapping
