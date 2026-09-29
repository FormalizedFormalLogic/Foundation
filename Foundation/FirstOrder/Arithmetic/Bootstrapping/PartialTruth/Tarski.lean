module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.HierarchicalSatisfaction

/-!
# The Tarski conditions as an explicit finite theory

The Tarski conditions for $\Delta_0$ satisfaction as explicit arithmetic sentences, together with
the agreement of its $\Sigma_1$ and $\Pi_1$ definitions, collected into the finite theory
`tarski`, which `𝗜𝚺₁` proves; and their readings, as well as those of the defining formulas of
`HierarchicalSatisfaction`, inside any model of `𝗣𝗔⁻` satisfying `tarski`.

## References

- [HP98, 1.64(5), Theorem I.1.70, Remark I.1.77]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

/-! ## The sentences -/

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

open Arithmetic.Tarski in
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

open Arithmetic.Tarski

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

open Arithmetic.Tarski in
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

theorem ISigma1.provable_tarski : 𝗜𝚺₁ ⊢* tarski := fun {_} hσ ↦
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ models_tarski hσ

/-! ## The readings of the defining formulas -/

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

/-! ## Reading the sentences in a model of `𝗣𝗔⁻` -/

section reading

open Reading PeanoMinus

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hV : ∀ σ ∈ tarski, V↓[ℒₒᵣ] ⊧ σ)

include hV

-- The readings are unfolded only here, to match them against the sentences of `tarski`.
attribute [local simp] models_iff Reading.BoundedSatisfaction Reading.HierarchicalSatisfaction
  Reading.Bounded Reading.UFormula Reading.UTerm Reading.Adjoin Reading.Nth Reading.Len
  Reading.TermVal

private lemma models_of_mem (σ : ArithmeticSentence) (hσ : σ ∈ tarski := by simp [tarski]) :
    V↓[ℒₒᵣ] ⊧ σ :=
  hV σ hσ

lemma read_boundedSatisfactionVerum : ∀ z e : V, V ⊧/![z] qqVerumDef.val →
    BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionVerum] using models_of_mem hV Tarski.boundedSatisfactionVerum;

lemma read_boundedSatisfactionFalsum : ∀ z e : V, V ⊧/![z] qqFalsumDef.val →
    ¬BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionFalsum] using models_of_mem hV Tarski.boundedSatisfactionFalsum;

lemma read_boundedSatisfactionEq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqEQDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt = vu) := by
  simpa [Tarski.boundedSatisfactionEq] using models_of_mem hV Tarski.boundedSatisfactionEq;

lemma read_boundedSatisfactionNeq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNEQDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt ≠ vu) := by
  simpa [Tarski.boundedSatisfactionNeq] using models_of_mem hV Tarski.boundedSatisfactionNeq;

lemma read_boundedSatisfactionLt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqLTDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt < vu) := by
  simpa [Tarski.boundedSatisfactionLt] using models_of_mem hV Tarski.boundedSatisfactionLt;

lemma read_boundedSatisfactionNlt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNLTDef.val → TermVal vt e t → TermVal vu e u →
    (BoundedSatisfaction z e ↔ ¬(vt < vu)) := by
  simpa [Tarski.boundedSatisfactionNlt] using models_of_mem hV Tarski.boundedSatisfactionNlt;

lemma read_boundedSatisfactionAnd : ∀ p q z e : V, V ⊧/![z, p, q] qqAndDef.val →
    (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionAnd] using models_of_mem hV Tarski.boundedSatisfactionAnd;

lemma read_boundedSatisfactionOr : ∀ p q z e : V, Reading.Bounded p → UFormula p →
    Reading.Bounded q → UFormula q →
    V ⊧/![z, p, q] qqOrDef.val →
      (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionOr] using models_of_mem hV Tarski.boundedSatisfactionOr;

lemma read_boundedSatisfactionBall : ∀ t u q z e v : V, UTerm t → Reading.Bounded q → UFormula q →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBallDef.val → TermVal v e t →
    (BoundedSatisfaction z e ↔ ∀ x < v, ∀ e', Adjoin e' x e → BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBall] using models_of_mem hV Tarski.boundedSatisfactionBall;

lemma read_boundedSatisfactionBex : ∀ t u q z e v : V, UTerm t →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBexDef.val → TermVal v e t →
    (BoundedSatisfaction z e ↔ ∃ x < v, ∃ e', Adjoin e' x e ∧ BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBex] using models_of_mem hV Tarski.boundedSatisfactionBex;

lemma read_termValBvar : ∀ e z t v : V, V ⊧/![t, z] qqBvarDef.val →
    (TermVal v e t ↔ Nth v e z) := by
  simpa [Tarski.termValBvar] using models_of_mem hV Tarski.termValBvar;

lemma read_termValZero : ∀ e v : V, TermVal v e ((𝟎 : ℕ) : V) ↔ v = 0 := by
  simpa [Tarski.termValZero, numeral_eq_natCast] using models_of_mem hV Tarski.termValZero;

lemma read_termValOne : ∀ e v : V, TermVal v e ((𝟏 : ℕ) : V) ↔ v = 1 := by
  simpa [Tarski.termValOne, numeral_eq_natCast] using models_of_mem hV Tarski.termValOne;

lemma read_termValAdd : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqAddGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt + vu) := by
  simpa [Tarski.termValAdd] using models_of_mem hV Tarski.termValAdd;

lemma read_termValMul : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqMulGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt * vu) := by
  simpa [Tarski.termValMul] using models_of_mem hV Tarski.termValMul;

lemma read_adjoinTotal : ∀ x v : V, ∃ e, Adjoin e x v := by
  simpa [Tarski.adjoinTotal] using models_of_mem hV Tarski.adjoinTotal;

lemma read_nthAdjoinZero : ∀ x v e y : V, Adjoin e x v → (Nth y e 0 ↔ y = x) := by
  simpa [Tarski.nthAdjoinZero] using models_of_mem hV Tarski.nthAdjoinZero;

lemma read_nthAdjoinSucc : ∀ x v e i y : V, Adjoin e x v → (Nth y e (i + 1) ↔ Nth y v i) := by
  simpa [Tarski.nthAdjoinSucc] using models_of_mem hV Tarski.nthAdjoinSucc;

lemma read_lenNil : ∀ l : V, Len l 0 ↔ l = 0 := by
  simpa [Tarski.lenNil] using models_of_mem hV Tarski.lenNil;

lemma read_lenAdjoin : ∀ x v e l : V, Adjoin e x v → (Len (l + 1) e ↔ Len l v) := by
  simpa [Tarski.lenAdjoin] using models_of_mem hV Tarski.lenAdjoin;

lemma read_hierarchicalSatisfaction_pi_succ (s : ℕ) (p e : V) :
    HierarchicalSatisfaction 𝚷 (s + 1) p e ↔
      ∀ x e', Adjoin e' x e → HierarchicalSatisfaction 𝚺 s p e' := by
  have h := models_of_mem hV Tarski.boundedSatisfactionProper;
  cases s <;> simp_all [Tarski.boundedSatisfactionProper, hierarchicalSatisfactionDef,
    hierarchicalSatisfaction, hierarchicalSatisfaction', HierarchySymbol.Semiformula.val_sigma];

end reading

end FFL.FirstOrder.Arithmetic
