module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Tarski
public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Partial truth definitions agree with truth

For a sentence `φ` in `Γ`-prenex form of level `s` with a $\Delta_0$ matrix,
`PartialTruth Γ s ⌜φ⌝` holds exactly when `φ` does, in every model of `𝗜𝚺₁`; hence `𝗜𝚺₁` proves
the Tarski biconditional `partialTruthDef Γ s (⌜φ⌝) ↔ φ`. For formulas with free variables,
satisfaction of the code of the matrix agrees with truth, both in every model of `𝗜𝚺₁` and,
uniformly in the level, over `𝗣𝗔⁻` together with the finite Tarski theory `tarski`.

## References

- [HP98, 0.30, 1.66, Lemma I.1.68, Theorem I.1.70, Definition I.1.74, Corollary I.1.76,
  Remark I.1.77, Remark I.1.80]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

section cast

variable {a b : ℕ} (h : a = b) {θ : ArithmeticSemisentence a}

private lemma closure_cast (hθ : ℬ[<, ℒₒᵣ].Closure θ) :
    ℬ[<, ℒₒᵣ].Closure (cast (congrArg ArithmeticSemisentence h) θ) := by
  subst h; exact hθ

private lemma quote_cast {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (⌜cast (congrArg ArithmeticSemisentence h) θ⌝ : V) = ⌜θ⌝ := by
  subst h; rfl

end cast

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
    simp [← ihφ, Function.comp_def];
  · intro n t φ hφ ihφ v;
    rw [quote_bex_sentence, BoundedSatisfaction.bex_iff (by simp), termVal_quote];
    simp [← ihφ, Function.comp_def];

private lemma hierarchicalSatisfaction_quote_toPrenex_iff : ∀ {Γ : Polarity} {s k : ℕ}
    {θ : ArithmeticSemisentence (k + s)}, ℬ[<, ℒₒᵣ].Closure θ → ∀ v : Fin k → V,
      HierarchicalSatisfaction Γ s (⌜θ⌝ : V) (matrixToVec v) ↔ V ⊧/v (θ.toPrenex Γ s)
  | _, 0, _, _, hθ, v => by simpa using boundedSatisfaction_quote_iff hθ v
  | 𝚺, s + 1, k, θ, hθ, v => by
    have ih := hierarchicalSatisfaction_quote_toPrenex_iff (Γ := 𝚷)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];
  | 𝚷, s + 1, k, θ, hθ, v => by
    have ih := hierarchicalSatisfaction_quote_toPrenex_iff (Γ := 𝚺)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];

theorem hierarchicalSatisfaction_quote_iff {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k)
    (v : Fin k → V) :
    HierarchicalSatisfaction Γ s (⌜φ.matrix.val⌝ : V) (matrixToVec v) ↔ V ⊧/v φ.val :=
  hierarchicalSatisfaction_quote_toPrenex_iff φ.matrix.bounded v

/-! ## Partial truth -/

lemma quote_toPrenex : ∀ {Γ : Polarity} {s n : ℕ} (θ : ArithmeticSemisentence (n + s)),
    (⌜θ.toPrenex Γ s⌝ : V) = qqToPrenex Γ s ⌜θ⌝
  | _, 0, _, _ => by simp
  | 𝚺, s + 1, n, θ => by
    simp [Polarity.quantItr_succ, quote_toPrenex (Γ := 𝚷), quote_cast (Nat.succ_add n s).symm]
  | 𝚷, s + 1, n, θ => by
    simp [Polarity.quantItr_succ, quote_toPrenex (Γ := 𝚺), quote_cast (Nat.succ_add n s).symm]

theorem partialTruth_quote_iff {Γ : Polarity} {s : ℕ} (φ : Prenex Γ s Empty 0) :
    PartialTruth Γ s (⌜φ.val⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ φ.val := by
  have h := hierarchicalSatisfaction_quote_iff (V := V) φ ![];
  rw [matrixToVec_nil] at h;
  simpa [PartialTruth, Prenex.val, quote_toPrenex, models_iff] using h

theorem ISigma1.provable_partialTruth_iff {Γ : Polarity} {s : ℕ} (φ : Prenex Γ s Empty 0) :
    𝗜𝚺₁ ⊢ (partialTruthDef Γ s)/[⌜φ.val⌝] 🡘 φ.val :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff, eval_partialTruthDef] using partialTruth_quote_iff φ

/-! ## The disquotation sentences -/

noncomputable def hierarchicalSatisfactionVec (Γ : Polarity) (s k : ℕ) :
    ArithmeticSemisentence (k + 1) :=
  “p. ∃ e, !lenDef ↑k e ∧ (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(hierarchicalSatisfactionDef Γ s) p e”

noncomputable def disquotation {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k) :
    ArithmeticSentence :=
  ∀¹* (φ.val 🡘 (hierarchicalSatisfactionVec Γ s k) ⇜
    ((⌜φ.matrix.val⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

/-! ## The disquotation lemma over `𝗣𝗔⁻` -/

section peanoMinus

open _root_.FFL.FirstOrder.Tarski Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
  (hM : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ)

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
      rw [show (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟎 by
        simp];
      exact (read_termValZero hM ev 0).mpr rfl;
    | 0, .one, w, _ =>
      rw [show (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟏 by
        simp];
      exact (read_termValOne hM ev 1).mpr rfl;
    | 2, .add, w, ih =>
      have hq : M ⊧/![((⌜Semiterm.func Language.ORing.Func.add w⌝ : ℕ) : M), ((⌜w 0⌝ : ℕ) : M),
          ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqAddGraph (by simp);
      exact (read_termValAdd hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;
    | 2, .mul, w, ih =>
      have hq : M ⊧/![((⌜Semiterm.func Language.ORing.Func.mul w⌝ : ℕ) : M), ((⌜w 0⌝ : ℕ) : M),
          ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        sigmaOne_upward_absolute₃ Arithmetic.qqMulGraph (by simp);
      exact (read_termValMul hM ev _ _ _ _ _ _ (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq
        (ih 0) (ih 1)).mpr rfl;

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

end peanoMinus

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

theorem ISigma1.provable_disquotation {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k) :
    𝗜𝚺₁ ⊢ disquotation φ := by
  have : 𝗣𝗔⁻ ∪ tarski ⪯ 𝗜𝚺₁ := Entailment.WeakerThan.ofAxm! fun {σ} hσ ↦ by
    rcases hσ with h | h;
    · exact Entailment.WeakerThan.pbl (Entailment.by_axm h);
    · exact ISigma1.provable_tarski h;
  exact this.pbl (provable_disquotation_of_tarski φ);

end FFL.FirstOrder.Arithmetic
