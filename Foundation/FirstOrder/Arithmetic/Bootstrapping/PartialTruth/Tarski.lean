module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.HierarchicalSatisfaction

/-!
# The Tarski conditions as an explicit finite theory

The Tarski conditions for the partial truth definitions as explicit arithmetic sentences,
collected into the finite theory `tarski n`, which `𝗜𝚺₁` proves; and their readings inside any
model of `𝗣𝗔⁻` satisfying `tarski n`.

## References

- [HP98, 1.64(5), Theorem I.1.70, Theorem I.1.75(2), Remark I.1.77]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

/-! ## The sentences -/

namespace Tarski

noncomputable def boundedSatisfactionDom : ArithmeticSentence :=
  “∀ z e, !boundedSatisfaction.val z e → !isBounded.val z ∧ !(isUFormula ℒₒᵣ).val z”

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

-- Unlike conjunction, both disjuncts have to be assumed well-formed: one satisfied disjunct says
-- nothing about the shape of the other, while satisfaction of the disjunction carries the
-- well-formedness of both.
noncomputable def boundedSatisfactionOr : ArithmeticSentence :=
  “∀ p q z e, !isBounded.val p → !(isUFormula ℒₒᵣ).val p → !isBounded.val q →
    !(isUFormula ℒₒᵣ).val q → !qqOrDef.val z p q →
    (!boundedSatisfaction.val z e ↔ !boundedSatisfaction.val p e ∨ !boundedSatisfaction.val q e)”

noncomputable def boundedSatisfactionNeg : ArithmeticSentence :=
  “∀ p np e, !isBounded.val p → !(isUFormula ℒₒᵣ).val p →
    !(negGraph ℒₒᵣ).val np p → (!boundedSatisfaction.val np e ↔ ¬!boundedSatisfaction.val p e)”

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

noncomputable def adjoinUnique : ArithmeticSentence :=
  “∀ x v e e', !adjoinDef.val e x v → !adjoinDef.val e' x v → e = e'”

noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

noncomputable def nthAdjoinSucc : ArithmeticSentence := “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

noncomputable def sigmaSatisfactionOfPi : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isBounded.val z → !(isUFormula ℒₒᵣ).val z →
        (!(sigmaSatisfaction 0).val z e ↔ !boundedSatisfaction.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictHierarchy 𝚷 (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(sigmaSatisfaction (n + 1)).val z e ↔ !(piSatisfaction n).val z e)”

noncomputable def piSatisfactionOfSigma : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isBounded.val z → !(isUFormula ℒₒᵣ).val z →
        (!(piSatisfaction 0).val z e ↔ !boundedSatisfaction.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictHierarchy 𝚺 (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(piSatisfaction (n + 1)).val z e ↔ !(sigmaSatisfaction n).val z e)”

noncomputable def sigmaSatisfactionDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(sigmaSatisfaction n).val z e →
    !(isStrictHierarchy 𝚺 (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

noncomputable def piSatisfactionDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(piSatisfaction n).val z e →
    !(isStrictHierarchy 𝚷 (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

noncomputable def sigmaSatisfactionExs (n : ℕ) : ArithmeticSentence := “∀ p z e, !qqExsDef.val z p →
    (!(sigmaSatisfaction n).val z e ↔ ∃ x e', !adjoinDef.val e' x e ∧
      !(sigmaSatisfaction n).val p e')”

noncomputable def piSatisfactionAll (n : ℕ) : ArithmeticSentence := “∀ p z e, !qqAllDef.val z p →
    (!(piSatisfaction n).val z e ↔ ∀ x e', !adjoinDef.val e' x e → !(piSatisfaction n).val p e')”

noncomputable def piSatisfactionNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictHierarchy 𝚺 (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(piSatisfaction n).val nz e ↔ ¬!(sigmaSatisfaction n).val z e)”

noncomputable def sigmaSatisfactionNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictHierarchy 𝚷 (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(sigmaSatisfaction n).val nz e ↔ ¬!(piSatisfaction n).val z e)”

noncomputable def boundedSatisfactionAxioms : ArithmeticTheory := {
  boundedSatisfactionDom,
  boundedSatisfactionVerum,
  boundedSatisfactionFalsum,
  boundedSatisfactionEq,
  boundedSatisfactionNeq,
  boundedSatisfactionLt,
  boundedSatisfactionNlt,
  boundedSatisfactionAnd,
  boundedSatisfactionOr,
  boundedSatisfactionNeg,
  boundedSatisfactionBall,
  boundedSatisfactionBex,
  termValBvar,
  termValZero,
  termValOne,
  termValAdd,
  termValMul,
  adjoinTotal,
  adjoinUnique,
  nthAdjoinZero,
  nthAdjoinSucc,
  lenNil,
  lenAdjoin
}

noncomputable def sigmaSatisfactionAxioms (n : ℕ) : ArithmeticTheory := {
  sigmaSatisfactionOfPi n,
  piSatisfactionOfSigma n,
  sigmaSatisfactionDom n,
  piSatisfactionDom n,
  sigmaSatisfactionExs n,
  piSatisfactionAll n,
  piSatisfactionNeg n,
  sigmaSatisfactionNeg n
}

lemma boundedSatisfactionAxioms_finite : boundedSatisfactionAxioms.Finite := by
  simp [boundedSatisfactionAxioms];

lemma sigmaSatisfactionAxioms_finite (n : ℕ) : (sigmaSatisfactionAxioms n).Finite := by
  simp [sigmaSatisfactionAxioms];

end Tarski

inductive tarski : ℕ → ArithmeticTheory
  | zero : ∀ n, ∀ φ ∈ Tarski.boundedSatisfactionAxioms, tarski n φ
  | prev : ∀ n φ, tarski n φ → tarski (n + 1) φ
  | new  : ∀ n, ∀ φ ∈ Tarski.sigmaSatisfactionAxioms n, tarski n φ

lemma tarski_zero : tarski 0 = Tarski.boundedSatisfactionAxioms ∪
    Tarski.sigmaSatisfactionAxioms 0 := by
  ext φ;
  constructor;
  · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩);
    · exact Set.mem_union_left _ h;
    · exact Set.mem_union_right _ h;
  · rintro (h | h);
    · exact tarski.zero 0 φ h;
    · exact tarski.new 0 φ h;

lemma tarski_succ (n : ℕ) : tarski (n + 1) = tarski n ∪ Tarski.sigmaSatisfactionAxioms (n + 1) := by
  ext φ;
  constructor;
  · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩);
    · exact Set.mem_union_left _ (tarski.zero n φ h);
    · exact Set.mem_union_left _ h;
    · exact Set.mem_union_right _ h;
  · rintro (h | h);
    · exact tarski.prev n φ h;
    · exact tarski.new (n + 1) φ h;

lemma tarski_finite (n : ℕ) : (tarski n).Finite := by
  induction n with
  | zero =>
    rw [tarski_zero];
    exact Tarski.boundedSatisfactionAxioms_finite.union (Tarski.sigmaSatisfactionAxioms_finite 0);
  | succ n ih =>
    rw [tarski_succ];
    exact ih.union (Tarski.sigmaSatisfactionAxioms_finite (n + 1));

lemma tarski_mono {m n : ℕ} (hmn : m ≤ n) {σ : ArithmeticSentence} (h : tarski m σ) :
    tarski n σ := by
  induction hmn with
  | refl => exact h;
  | step _ ih => exact tarski.prev _ σ ih;

/-! ## The level of the Tarski conditions in the arithmetical hierarchy -/

namespace Tarski

section Hierarchy

variable {s m : ℕ}

-- Each Tarski sentence is a universal closure of a Boolean combination of formulas of level at
-- most `𝚺 (m + 1)`: `iff_iff` splits the biconditionals, and `dummy_sigma`, `dummy_pi` absorb the
-- quantifier blocks that raise the level by one.
attribute [local simp] Bounding.Hierarchy.iff_iff Bounding.Hierarchy.dummy_sigma
  Bounding.Hierarchy.dummy_pi

lemma hierarchy_of_mem_boundedSatisfactionAxioms {σ : ArithmeticSentence}
    (hσ : σ ∈ boundedSatisfactionAxioms) : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (s + 3) σ := by
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boundedSatisfactionDom, boundedSatisfactionVerum, boundedSatisfactionFalsum,
      boundedSatisfactionEq, boundedSatisfactionNeq, boundedSatisfactionLt, boundedSatisfactionNlt,
      boundedSatisfactionAnd, boundedSatisfactionOr, boundedSatisfactionNeg,
      boundedSatisfactionBall, boundedSatisfactionBex, termValBvar, termValZero, termValOne,
      termValAdd, termValMul, adjoinTotal, adjoinUnique, nthAdjoinZero, nthAdjoinSucc, lenNil,
      lenAdjoin];

lemma hierarchy_of_mem_sigmaSatisfactionAxioms {σ : ArithmeticSentence}
    (hσ : σ ∈ sigmaSatisfactionAxioms m) : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 2) σ := by
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases m <;>
    simp [sigmaSatisfactionOfPi, piSatisfactionOfSigma, sigmaSatisfactionDom, piSatisfactionDom,
      sigmaSatisfactionExs, piSatisfactionAll, piSatisfactionNeg, sigmaSatisfactionNeg];

end Hierarchy

end Tarski

lemma hierarchy_of_tarski {n : ℕ} {σ : ArithmeticSentence} (hσ : tarski n σ) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (n + 3) σ := by
  induction hσ with
  | zero n φ hφ => exact Tarski.hierarchy_of_mem_boundedSatisfactionAxioms hφ;
  | prev n φ _ ih => exact ih.mono (by omega);
  | new n φ hφ => exact (Tarski.hierarchy_of_mem_sigmaSatisfactionAxioms hφ).mono (by omega);

/-! ## `𝗜𝚺₁` proves the Tarski conditions -/

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Tarski

lemma models_boundedSatisfactionDom : V↓[ℒₒᵣ] ⊧ boundedSatisfactionDom := by
  suffices ∀ z e : V, BoundedSatisfaction z e → IsBounded z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, boundedSatisfactionDom] using this;
  exact fun _ _ h ↦ BoundedSatisfaction.dom h;

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

lemma models_boundedSatisfactionNeg : V↓[ℒₒᵣ] ⊧ boundedSatisfactionNeg := by
  suffices ∀ p np e : V, IsBounded p → IsUFormula ℒₒᵣ p → np = neg ℒₒᵣ p →
      (BoundedSatisfaction np e ↔ ¬BoundedSatisfaction p e) by
    simpa [models_iff, boundedSatisfactionNeg] using this;
  rintro p _ e hd hf rfl;
  exact BoundedSatisfaction.neg_iff hd hf;

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

lemma models_adjoinUnique : V↓[ℒₒᵣ] ⊧ adjoinUnique := by
  simp [models_iff, adjoinUnique];

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

lemma models_sigmaSatisfactionOfPi (n : ℕ) : V↓[ℒₒᵣ] ⊧ sigmaSatisfactionOfPi n := by
  cases n with
  | zero =>
    suffices ∀ z e : V, IsBounded z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction 1 z e ↔ BoundedSatisfaction z e) by
      simpa [models_iff, sigmaSatisfactionOfPi] using this;
    intro z e hd hf;
    rw [SigmaSatisfaction.of_pi (IsStrictHierarchy.of_bounded hd) hf, PiSatisfaction.zero];
  | succ n =>
    suffices ∀ z e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction (n + 2) z e ↔ PiSatisfaction (n + 1) z e) by
      simpa [models_iff, sigmaSatisfactionOfPi] using this;
    intro z e hs hf;
    exact SigmaSatisfaction.of_pi hs hf;

lemma models_piSatisfactionOfSigma (n : ℕ) : V↓[ℒₒᵣ] ⊧ piSatisfactionOfSigma n := by
  cases n with
  | zero =>
    suffices ∀ z e : V, IsBounded z → IsUFormula ℒₒᵣ z →
      (PiSatisfaction 1 z e ↔ BoundedSatisfaction z e) by
      simpa [models_iff, piSatisfactionOfSigma] using this;
    intro z e hd hf;
    rw [PiSatisfaction.of_sigma (IsStrictHierarchy.of_bounded hd) hf, SigmaSatisfaction.zero];
  | succ n =>
    suffices ∀ z e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z →
        (PiSatisfaction (n + 2) z e ↔ SigmaSatisfaction (n + 1) z e) by
      simpa [models_iff, piSatisfactionOfSigma] using this;
    intro z e hs hf;
    exact PiSatisfaction.of_sigma hs hf;

lemma models_sigmaSatisfactionDom (n : ℕ) : V↓[ℒₒᵣ] ⊧ sigmaSatisfactionDom n := by
  suffices ∀ z e : V, SigmaSatisfaction (n + 1) z e → IsStrictSigma (n + 1) z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, sigmaSatisfactionDom] using this;
  exact fun _ _ h ↦ SigmaSatisfaction.dom h;

lemma models_piSatisfactionDom (n : ℕ) : V↓[ℒₒᵣ] ⊧ piSatisfactionDom n := by
  suffices ∀ z e : V, PiSatisfaction (n + 1) z e → IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, piSatisfactionDom] using this;
  exact fun _ _ h ↦ PiSatisfaction.dom h;

lemma models_sigmaSatisfactionExs (n : ℕ) : V↓[ℒₒᵣ] ⊧ sigmaSatisfactionExs n := by
  suffices ∀ p z e : V, z = ^∃ p →
    (SigmaSatisfaction (n + 1) z e ↔ ∃ x, SigmaSatisfaction (n + 1) p (x ∷ e)) by
    simpa [models_iff, sigmaSatisfactionExs] using this;
  rintro p _ e rfl;
  exact SigmaSatisfaction.exs_iff;

lemma models_piSatisfactionAll (n : ℕ) : V↓[ℒₒᵣ] ⊧ piSatisfactionAll n := by
  suffices ∀ p z e : V, z = ^∀ p →
    (PiSatisfaction (n + 1) z e ↔ ∀ x, PiSatisfaction (n + 1) p (x ∷ e)) by
    simpa [models_iff, piSatisfactionAll] using this;
  rintro p _ e rfl;
  exact PiSatisfaction.all_iff;

lemma models_piSatisfactionNeg (n : ℕ) : V↓[ℒₒᵣ] ⊧ piSatisfactionNeg n := by
  suffices ∀ z nz e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → nz = neg ℒₒᵣ z →
      (PiSatisfaction (n + 1) nz e ↔ ¬SigmaSatisfaction (n + 1) z e) by
    simpa [models_iff, piSatisfactionNeg] using this;
  rintro z _ e hs hf rfl;
  exact PiSatisfaction.neg_iff hs hf;

lemma models_sigmaSatisfactionNeg (n : ℕ) : V↓[ℒₒᵣ] ⊧ sigmaSatisfactionNeg n := by
  suffices ∀ z nz e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z → nz = neg ℒₒᵣ z →
      (SigmaSatisfaction (n + 1) nz e ↔ ¬PiSatisfaction (n + 1) z e) by
    simpa [models_iff, sigmaSatisfactionNeg] using this;
  rintro z _ e hs hf rfl;
  exact SigmaSatisfaction.neg_iff hs hf;

lemma models_boundedSatisfactionAxioms {φ : ArithmeticSentence}
    (h : φ ∈ boundedSatisfactionAxioms) :
    V↓[ℒₒᵣ] ⊧ φ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
  exacts [models_boundedSatisfactionDom, models_boundedSatisfactionVerum,
    models_boundedSatisfactionFalsum, models_boundedSatisfactionEq,
    models_boundedSatisfactionNeq, models_boundedSatisfactionLt, models_boundedSatisfactionNlt,
    models_boundedSatisfactionAnd, models_boundedSatisfactionOr,
    models_boundedSatisfactionNeg, models_boundedSatisfactionBall, models_boundedSatisfactionBex,
    models_termValBvar, models_termValZero, models_termValOne, models_termValAdd,
    models_termValMul, models_adjoinTotal, models_adjoinUnique, models_nthAdjoinZero,
    models_nthAdjoinSucc, models_lenNil, models_lenAdjoin];

lemma models_sigmaSatisfactionAxioms {n : ℕ} {φ : ArithmeticSentence}
    (h : φ ∈ sigmaSatisfactionAxioms n) :
    V↓[ℒₒᵣ] ⊧ φ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
  exacts [models_sigmaSatisfactionOfPi n, models_piSatisfactionOfSigma n,
    models_sigmaSatisfactionDom n, models_piSatisfactionDom n,
    models_sigmaSatisfactionExs n, models_piSatisfactionAll n, models_piSatisfactionNeg n,
    models_sigmaSatisfactionNeg n];

end Tarski

lemma models_tarski {n : ℕ} {φ : ArithmeticSentence} (h : tarski n φ) : V↓[ℒₒᵣ] ⊧ φ := by
  induction h with
  | zero _ _ h => exact Tarski.models_boundedSatisfactionAxioms h;
  | prev _ _ _ ih => exact ih;
  | new _ _ h => exact Tarski.models_sigmaSatisfactionAxioms h;

end models

theorem ISigma1.provable_tarski (n : ℕ) : 𝗜𝚺₁ ⊢* tarski n := fun {_} hφ ↦
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ models_tarski hφ

/-! ## The readings of the defining formulas -/

namespace Reading

variable {V : Type*} [ORingStructure V]

def BoundedSatisfaction (z e : V) : Prop := V ⊧/![z, e] boundedSatisfaction.val

def SigmaSatisfaction (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (sigmaSatisfaction m).val

def PiSatisfaction (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (piSatisfaction m).val

def HierarchicalSatisfaction : Polarity → ℕ → V → V → Prop
  | _,       0     => BoundedSatisfaction
  | .sigma, m + 1 => Reading.SigmaSatisfaction m
  | .pi,    m + 1 => Reading.PiSatisfaction m

def Bounded (z : V) : Prop := V ⊧/![z] isBounded.val

def UFormula (z : V) : Prop := V ⊧/![z] (isUFormula ℒₒᵣ).val

def UTerm (t : V) : Prop := V ⊧/![t] (isUTerm ℒₒᵣ).val

def Strict (Γ : Polarity) (m : ℕ) (z : V) : Prop := V ⊧/![z] (isStrictHierarchy Γ m).val

def Adjoin (e' x e : V) : Prop := V ⊧/![e', x, e] adjoinDef.val

def Nth (y e i : V) : Prop := V ⊧/![y, e, i] nthDef.val

def Len (l e : V) : Prop := V ⊧/![l, e] lenDef.val

def TermVal (y e t : V) : Prop := V ⊧/![y, e, t] termValGraph.val

end Reading

/-! ## Reading the sentences in a model of `𝗣𝗔⁻` -/

section reading

open Reading PeanoMinus

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hV : ∀ σ : ArithmeticSentence, tarski n σ → V↓[ℒₒᵣ] ⊧ σ)

include hV

-- The readings are unfolded only here, to match them against the sentences of `tarski n`.
attribute [local simp] models_iff Reading.BoundedSatisfaction Reading.SigmaSatisfaction
  Reading.PiSatisfaction Reading.HierarchicalSatisfaction Reading.Bounded Reading.UFormula
  Reading.UTerm Reading.Strict Reading.Adjoin Reading.Nth Reading.Len Reading.TermVal

section boundedSatisfaction

private lemma models_bounded (σ : ArithmeticSentence)
    (hσ : σ ∈ Tarski.boundedSatisfactionAxioms := by simp [Tarski.boundedSatisfactionAxioms]) :
    V↓[ℒₒᵣ] ⊧ σ :=
  hV σ (tarski.zero n σ hσ)

lemma read_boundedSatisfactionVerum : ∀ z e : V, V ⊧/![z] qqVerumDef.val →
    BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionVerum] using models_bounded hV Tarski.boundedSatisfactionVerum;

lemma read_boundedSatisfactionFalsum : ∀ z e : V, V ⊧/![z] qqFalsumDef.val →
    ¬BoundedSatisfaction z e := by
  simpa [Tarski.boundedSatisfactionFalsum] using models_bounded hV Tarski.boundedSatisfactionFalsum;

lemma read_boundedSatisfactionEq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqEQDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt = vu) := by
  simpa [Tarski.boundedSatisfactionEq] using models_bounded hV Tarski.boundedSatisfactionEq;

lemma read_boundedSatisfactionNeq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNEQDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt ≠ vu) := by
  simpa [Tarski.boundedSatisfactionNeq] using models_bounded hV Tarski.boundedSatisfactionNeq;

lemma read_boundedSatisfactionLt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqLTDef.val → TermVal vt e t → TermVal vu e u →
      (BoundedSatisfaction z e ↔ vt < vu) := by
  simpa [Tarski.boundedSatisfactionLt] using models_bounded hV Tarski.boundedSatisfactionLt;

lemma read_boundedSatisfactionNlt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNLTDef.val → TermVal vt e t → TermVal vu e u →
    (BoundedSatisfaction z e ↔ ¬(vt < vu)) := by
  simpa [Tarski.boundedSatisfactionNlt] using models_bounded hV Tarski.boundedSatisfactionNlt;

lemma read_boundedSatisfactionAnd : ∀ p q z e : V, V ⊧/![z, p, q] qqAndDef.val →
    (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionAnd] using models_bounded hV Tarski.boundedSatisfactionAnd;

lemma read_boundedSatisfactionOr : ∀ p q z e : V, Reading.Bounded p → UFormula p →
    Reading.Bounded q → UFormula q →
    V ⊧/![z, p, q] qqOrDef.val →
      (BoundedSatisfaction z e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e) := by
  simpa [Tarski.boundedSatisfactionOr] using models_bounded hV Tarski.boundedSatisfactionOr;

lemma read_boundedSatisfactionBall : ∀ t u q z e v : V, UTerm t → Reading.Bounded q → UFormula q →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBallDef.val → TermVal v e t →
    (BoundedSatisfaction z e ↔ ∀ x < v, ∀ e', Adjoin e' x e → BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBall] using models_bounded hV Tarski.boundedSatisfactionBall;

lemma read_boundedSatisfactionBex : ∀ t u q z e v : V, UTerm t →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBexDef.val → TermVal v e t →
    (BoundedSatisfaction z e ↔ ∃ x < v, ∃ e', Adjoin e' x e ∧ BoundedSatisfaction q e') := by
  simpa [Tarski.boundedSatisfactionBex] using models_bounded hV Tarski.boundedSatisfactionBex;

lemma read_termValBvar : ∀ e z t v : V, V ⊧/![t, z] qqBvarDef.val →
    (TermVal v e t ↔ Nth v e z) := by
  simpa [Tarski.termValBvar] using models_bounded hV Tarski.termValBvar;

lemma read_termValZero : ∀ e v : V, TermVal v e ((𝟎 : ℕ) : V) ↔ v = 0 := by
  simpa [Tarski.termValZero, numeral_eq_natCast] using models_bounded hV Tarski.termValZero;

lemma read_termValOne : ∀ e v : V, TermVal v e ((𝟏 : ℕ) : V) ↔ v = 1 := by
  simpa [Tarski.termValOne, numeral_eq_natCast] using models_bounded hV Tarski.termValOne;

lemma read_termValAdd : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqAddGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt + vu) := by
  simpa [Tarski.termValAdd] using models_bounded hV Tarski.termValAdd;

lemma read_termValMul : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqMulGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt * vu) := by
  simpa [Tarski.termValMul] using models_bounded hV Tarski.termValMul;

lemma read_adjoinTotal : ∀ x v : V, ∃ e, Adjoin e x v := by
  simpa [Tarski.adjoinTotal] using models_bounded hV Tarski.adjoinTotal;

lemma read_nthAdjoinZero : ∀ x v e y : V, Adjoin e x v → (Nth y e 0 ↔ y = x) := by
  simpa [Tarski.nthAdjoinZero] using models_bounded hV Tarski.nthAdjoinZero;

lemma read_nthAdjoinSucc : ∀ x v e i y : V, Adjoin e x v → (Nth y e (i + 1) ↔ Nth y v i) := by
  simpa [Tarski.nthAdjoinSucc] using models_bounded hV Tarski.nthAdjoinSucc;

lemma read_lenNil : ∀ l : V, Len l 0 ↔ l = 0 := by
  simpa [Tarski.lenNil] using models_bounded hV Tarski.lenNil;

lemma read_lenAdjoin : ∀ x v e l : V, Adjoin e x v → (Len (l + 1) e ↔ Len l v) := by
  simpa [Tarski.lenAdjoin] using models_bounded hV Tarski.lenAdjoin;

end boundedSatisfaction

section sigmaSatisfaction

variable {m : ℕ} (hm : m ≤ n)

include hm

private lemma models_sigma (σ : ArithmeticSentence)
    (hσ : σ ∈ Tarski.sigmaSatisfactionAxioms m := by simp [Tarski.sigmaSatisfactionAxioms]) :
    V↓[ℒₒᵣ] ⊧ σ :=
  hV σ (tarski_mono hm (tarski.new m σ hσ))

lemma read_sigmaSatisfactionOfPi : ∀ z e : V, Strict 𝚷 m z → Reading.UFormula z →
    (Reading.SigmaSatisfaction m z e ↔ HierarchicalSatisfaction 𝚷 m z e) := by
  have h := models_sigma hV hm (Tarski.sigmaSatisfactionOfPi m);
  cases m <;> simpa [Tarski.sigmaSatisfactionOfPi, isStrictHierarchy] using h;

lemma read_piSatisfactionOfSigma : ∀ z e : V, Strict 𝚺 m z → Reading.UFormula z →
    (Reading.PiSatisfaction m z e ↔ HierarchicalSatisfaction 𝚺 m z e) := by
  have h := models_sigma hV hm (Tarski.piSatisfactionOfSigma m);
  cases m <;> simpa [Tarski.piSatisfactionOfSigma, isStrictHierarchy] using h;

lemma read_ofAlt (Γ : Polarity) : ∀ z e : V, Strict Γ.alt m z → Reading.UFormula z →
    (HierarchicalSatisfaction Γ (m + 1) z e ↔ HierarchicalSatisfaction Γ.alt m z e) := by
  rcases Γ with _ | _;
  · exact read_sigmaSatisfactionOfPi hV hm;
  · exact read_piSatisfactionOfSigma hV hm;

lemma read_sigmaSatisfactionExs : ∀ p z e : V, V ⊧/![z, p] qqExsDef.val →
    (Reading.SigmaSatisfaction m z e ↔ ∃ x e', Adjoin e' x e ∧
      Reading.SigmaSatisfaction m p e') := by
  simpa [Tarski.sigmaSatisfactionExs] using models_sigma hV hm (Tarski.sigmaSatisfactionExs m);

lemma read_piSatisfactionAll : ∀ p z e : V, V ⊧/![z, p] qqAllDef.val →
    (Reading.PiSatisfaction m z e ↔ ∀ x e', Adjoin e' x e → Reading.PiSatisfaction m p e') := by
  simpa [Tarski.piSatisfactionAll] using models_sigma hV hm (Tarski.piSatisfactionAll m);

end sigmaSatisfaction

end reading

end FFL.FirstOrder.Arithmetic
