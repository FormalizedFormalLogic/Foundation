module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Tarski

/-!
# Partial truth definitions agree with truth

The “it's disquotation” agreement between partial satisfaction and semantics, both in every model of
`𝗜𝚺₁` and, uniformly, over `𝗣𝗔⁻` together with the finite Tarski theory `tarski n`.

## References

- [HP98, 0.30, 1.66, Lemma I.1.68, Lemma I.1.69, Theorem I.1.70, Definition I.1.74,
  Corollary I.1.76, Remark I.1.77, Remark I.1.80]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Agreement of satisfaction with truth -/

theorem boundedSatisfaction_quote_iff {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) (v : Fin k → V) :
    BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  revert hφ v;
  apply Bounding.Closure.arithmetic_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ v : Fin k → V, BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ);
  · intro n v; simp [Sentence.quote_verum];
  · intro n v; simp [Sentence.quote_falsum];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_rel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_nrel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_rel];
  · intro n t u v; simp [termVal_quote, Semiformula.eval_nrel];
  · intro n φ ψ hφ hψ ihφ ihψ v; simp [ihφ v, ihψ v];
  · intro n φ ψ hφ hψ ihφ ihψ v; simp [isBounded_quote_iff, hφ, hψ, ihφ v, ihψ v];
  · intro n t φ hφ ihφ v;
    rw [quote_ball_sentence, BoundedSatisfaction.ball_iff (by simp) ((isBounded_quote_iff φ).mpr hφ)
      (by simp), termVal_quote];
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel];
    apply forall_congr';
    intro x;
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)];
    simp [Function.comp_def];
  · intro n t φ hφ ihφ v;
    rw [quote_bex_sentence, BoundedSatisfaction.bex_iff (by simp), termVal_quote];
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel];
    apply exists_congr;
    intro x;
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)];
    simp [Function.comp_def];

lemma hierarchicalSatisfaction_quote_iff {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) :
    ∀ v : Fin k → V, HierarchicalSatisfaction Γ s (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    intro v;
    rcases Γ₀ with _ | _;
    · change SigmaSatisfaction 0 _ _ ↔ _;
      rw [SigmaSatisfaction.zero]; exact boundedSatisfaction_quote_iff hφ₀ v;
    · change PiSatisfaction 0 _ _ ↔ _;
      rw [PiSatisfaction.zero]; exact boundedSatisfaction_quote_iff hφ₀ v;
  | @ofAlt Γ₀ s₀ n₀ φ₀ hφ₀ ih =>
    intro v;
    rcases Γ₀ with _ | _;
    · change SigmaSatisfaction (s₀ + 1) _ _ ↔ _;
      rw [SigmaSatisfaction.of_pi ((isStrictPi_quote_iff φ₀).mpr hφ₀) (by simp)];
      exact ih v;
    · change PiSatisfaction (s₀ + 1) _ _ ↔ _;
      rw [PiSatisfaction.of_sigma ((isStrictSigma_quote_iff φ₀).mpr hφ₀) (by simp)];
      exact ih v;
  | @exs s₀ n₀ φ₀ hφ₀ ih =>
    intro v;
    change SigmaSatisfaction (s₀ + 1) _ _ ↔ _;
    rw [Sentence.quote_ex, SigmaSatisfaction.exs_iff];
    simp only [Semiformula.eval_ex];
    apply exists_congr;
    intro x;
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp];
    exact ih (x :> v);
  | @all s₀ n₀ φ₀ hφ₀ ih =>
    intro v;
    change PiSatisfaction (s₀ + 1) _ _ ↔ _;
    rw [Sentence.quote_all, PiSatisfaction.all_iff];
    simp only [Semiformula.eval_all];
    apply forall_congr';
    intro x;
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp];
    exact ih (x :> v);

section
variable {n k : ℕ} {φ : ArithmeticSemisentence k}

theorem sigmaSatisfaction_quote_iff (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SigmaSatisfaction n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := hierarchicalSatisfaction_quote_iff hφ v

theorem piSatisfaction_quote_iff (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    PiSatisfaction n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := hierarchicalSatisfaction_quote_iff hφ v

end

noncomputable def disquotation (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (sigmaSatisfactionVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

theorem models_disquotation_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ disquotation n φ ↔
      ∀ v : Fin k → V, V ⊧/v φ ↔ SigmaSatisfaction (n + 1) ⌜φ⌝ (matrixToVec v) := by
  simp [disquotation, models_iff, (sigmaSatisfactionVec.defined n k).df, Function.comp_def];

theorem ISigma1.provable_disquotation {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ disquotation n φ := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  exact (models_disquotation_iff φ).mpr fun v ↦ (sigmaSatisfaction_quote_iff hφ v).symm;

/-! ## The disquotation lemma over `𝗣𝗔⁻` -/

section peanoMinus

open _root_.FFL.FirstOrder.Tarski Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ)

/-! ### Codes of finite sequences -/

namespace Reading

def Codes {m : ℕ} (v : Fin m → M) (ev : M) : Prop :=
  Len (m : M) ev ∧ ∀ i : Fin m, Nth (v i) ev (i.val : M)

end Reading

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
private lemma termVal_quote_cast {k : ℕ} {v : Fin k → M} {ev : M} (hev : Codes v ev) :
    ∀ t : ClosedSemiterm ℒₒᵣ k, TermVal (t.valb v) ev ((⌜t⌝ : ℕ) : M) := by
  intro t;
  induction t with
  | bvar i =>
    have hb : M ⊧/![((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M), ((i.val : ℕ) : M)] qqBvarDef.val :=
      sigmaZero_upward_absolute₂ qqBvarDef (by simp);
    simpa using (read_termValBvar hM ev ((i.val : ℕ) : M) ((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
      (v i) hb).mpr (hev.2 i);
  | fvar x => exact x.elim;
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      have hq : (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟎 := by
        simp;
      rw [hq];
      exact (read_termValZero hM ev 0).mpr rfl;
    | 0, .one, w, _ =>
      have hq : (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟏 := by
        simp;
      rw [hq];
      exact (read_termValOne hM ev 1).mpr rfl;
    | 2, .add, w, ih =>
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.add w :
          ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqAddGraph
          (by simp);
      exact (read_termValAdd hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v + (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl;
    | 2, .mul, w, ih =>
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.mul w :
          ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqMulGraph
          (by simp);
      exact (read_termValMul hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v * (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl;

/-! ### The $\Delta_0$ base case -/

include hM in
private lemma boundedSatisfaction_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  revert hφ;
  apply Bounding.Closure.arithmetic_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ));
  · intro m v ev _;
    have hq : M ⊧/![((⌜(⊤ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqVerumDef.val :=
      sigmaZero_upward_absolute₁ qqVerumDef (by simp [Sentence.quote_verum]);
    simpa using read_boundedSatisfactionVerum hM _ ev hq;
  · intro m v ev _;
    have hq : M ⊧/![((⌜(⊥ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqFalsumDef.val :=
      sigmaZero_upward_absolute₁ qqFalsumDef (by simp [Sentence.quote_falsum]);
    simpa using read_boundedSatisfactionFalsum hM _ ev hq;
  · intro m t u v ev hev;
    have hq : M ⊧/![((⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqEQDef.val :=
      sigmaOne_upward_absolute₃ qqEQDef (by simp);
    rw [read_boundedSatisfactionEq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)];
    simp [Semiformula.eval_rel];
  · intro m t u v ev hev;
    have hq : M ⊧/![((⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNEQDef.val :=
      sigmaOne_upward_absolute₃ qqNEQDef (by simp);
    rw [read_boundedSatisfactionNeq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)];
    simp [Semiformula.eval_nrel];
  · intro m t u v ev hev;
    have hq : M ⊧/![((⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqLTDef.val :=
      sigmaOne_upward_absolute₃ qqLTDef (by simp);
    rw [read_boundedSatisfactionLt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)];
    simp [Semiformula.eval_rel];
  · intro m t u v ev hev;
    have hq : M ⊧/![((⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNLTDef.val :=
      sigmaOne_upward_absolute₃ qqNLTDef (by simp);
    rw [read_boundedSatisfactionNlt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)];
    simp [Semiformula.eval_nrel];
  · intro m φ ψ _ _ ihφ ihψ v ev hev;
    have hq : M ⊧/![((⌜φ ⋏ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqAndDef.val :=
      sigmaZero_upward_absolute₃ qqAndDef (by simp);
    rw [read_boundedSatisfactionAnd hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev hq, ihφ v ev hev,
      ihψ v ev hev];
    simp;
  · intro m φ ψ hφ hψ ihφ ihψ v ev hev;
    have hq : M ⊧/![((⌜φ ⋎ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqOrDef.val :=
      sigmaZero_upward_absolute₃ qqOrDef (by simp);
    rw [read_boundedSatisfactionOr hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev
      (bounded_quote_cast hφ) (uFormula_quote_cast φ) (bounded_quote_cast hψ)
      (uFormula_quote_cast ψ) hq, ihφ v ev hev, ihψ v ev hev];
    simp;
  · intro m t φ hφ ihφ v ev hev;
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := sigmaOne_upward_absolute₂ (termBShiftGraph ℒₒᵣ) (by simp);
    have hq : M ⊧/![((⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBallDef.val :=
      sigmaOne_upward_absolute₃ qqBallDef (by simpa using quote_ball_sentence (V := ℕ) t φ);
    rw [read_boundedSatisfactionBall hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) (bounded_quote_cast hφ)
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
    rw [read_boundedSatisfactionBex hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) hu hq
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

/-! ### The strict prenex induction -/

include hM in
private lemma hierarchicalSatisfaction_quote_reading {Γ : Polarity} {s k : ℕ}
    {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) (hs : s ≤ n + 1) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Reading.HierarchicalSatisfaction Γ s ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  revert hs;
  induction h with
  | @zero Γ₀ m₀ φ₀ hφ₀ =>
    intro _ v ev hev;
    exact boundedSatisfaction_quote_reading hM hφ₀ v ev hev;
  | @ofAlt Γ₀ s₀ m₀ φ₀ hφ₀ ih =>
    intro hs v ev hev;
    rw [read_ofAlt hM (show s₀ ≤ n by omega) Γ₀ ((⌜φ₀⌝ : ℕ) : M) ev
      (deltaOne_upward_absolute₁ (isStrictHierarchy Γ₀.alt s₀)
        (by simpa using (isStrictHierarchy_quote_iff (V := ℕ) φ₀).mpr hφ₀))
      (uFormula_quote_cast φ₀)];
    exact ih (by omega) v ev hev;
  | @exs s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev;
    have hq : M ⊧/![((⌜(∃¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqExsDef.val :=
      sigmaZero_upward_absolute₂ qqExsDef (by simp);
    change Reading.SigmaSatisfaction s₀ _ _ ↔ _;
    rw [read_sigmaSatisfactionExs hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq];
    simp only [Semiformula.eval_ex];
    constructor;
    · rintro ⟨x, e', hadj, hsat⟩;
      exact ⟨x, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩;
    · rintro ⟨x, hsat⟩;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact ⟨x, e', hadj, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr hsat⟩;
  | @all s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev;
    have hq : M ⊧/![((⌜(∀¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqAllDef.val :=
      sigmaZero_upward_absolute₂ qqAllDef (by simp);
    change Reading.PiSatisfaction s₀ _ _ ↔ _;
    rw [read_piSatisfactionAll hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq];
    simp only [Semiformula.eval_all];
    constructor;
    · intro hsat x;
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev;
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp (hsat x e' hadj);
    · intro hsat x e' hadj;
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr (hsat x);

include hM in
theorem sigmaSatisfaction_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) {v : Fin k → M} {ev : M} (hev : Codes v ev) :
    Reading.SigmaSatisfaction n ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ :=
  hierarchicalSatisfaction_quote_reading hM hφ le_rfl v ev hev

/-! ### Assembling the disquotation lemma over `𝗣𝗔⁻` -/

private lemma eval_sigmaSatisfactionVec {k : ℕ} (p : M) (w : Fin k → M) :
    M ⊧/(p :> w) (sigmaSatisfactionVec n k).val ↔
      ∃ ev, Codes w ev ∧ Reading.SigmaSatisfaction n p ev := by
  simp only [sigmaSatisfactionVec, Nat.succ_eq_add_one, Nat.reduceAdd,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app, Semiterm.val_bvar, Matrix.cons_val_zero, Fin.isValue, Fin.Fin1.eq_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃,
    Semiformula.eval_operator, Matrix.cons_val_succ, Tarski.Structure.eq_iff_eq,
    LogicalConnective.Prop.and_eq, exists_eq_right, Reading.Codes, Reading.Len, Reading.Nth,
    Reading.SigmaSatisfaction, and_assoc];

private lemma eval_disquotation_rhs {k : ℕ} (φ : ArithmeticSemisentence k) (e : Fin k → M) :
    M ⊧/e ((sigmaSatisfactionVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))
      ↔ M ⊧/(((⌜φ⌝ : ℕ) : M) :> e) (sigmaSatisfactionVec n k).val := by
  simp only [Semiformula.eval_substs, Matrix.comp_vecCons'', Arithmetic.gödelNumber'_def,
    Semiterm.Operator.encode, Semiterm.Operator.const, Semiterm.val_operator,
    Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app, Sentence.quote_eq_encode_nat,
    Matrix.empty_eq];
  simp only [Function.comp_def, Semiterm.val_bvar];

end peanoMinus

theorem provable_disquotation_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ disquotation n φ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ ∪ tarski n) := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance
      (Entailment.Axiomatized.le_of_subset Set.subset_union_left);
  unfold disquotation;
  apply Arithmetic.provable_iff_of_models_iff.{0} (T := 𝗣𝗔⁻ ∪ tarski n);
  intro M _ hMT e;
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := Semantics.ModelsSet.of_subset hMT Set.subset_union_left;
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun σ hσ ↦
    Semantics.ModelsSet.models _ (Set.mem_union_right 𝗣𝗔⁻ hσ);
  rw [eval_disquotation_rhs, eval_sigmaSatisfactionVec];
  constructor;
  · intro h;
    obtain ⟨ev, hev⟩ := exists_codes hM e;
    exact ⟨ev, hev, (hierarchicalSatisfaction_quote_reading hM hφ le_rfl e ev hev).mpr h⟩;
  · rintro ⟨ev, hev, hsat⟩;
    exact (hierarchicalSatisfaction_quote_reading hM hφ le_rfl e ev hev).mp hsat;

end FFL.FirstOrder.Arithmetic
