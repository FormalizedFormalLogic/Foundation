module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# $\Delta_1$ and r.e. presentations of arithmetic theories

The induction schemata over all formulas, over `ℬ[<, ℒₒᵣ].Hierarchy Γ s` and over the strict
prenex classes are `Δ₁`, hence so are `𝗣𝗔`, `𝗜𝗡𝗗⁺ Γ s` (in particular `𝗜𝚺⁺ n`) and `𝗜𝗡𝗗 Γ s`;
`𝗣𝗔` and `𝗜𝗡𝗗⁺ Γ s` are also recursively enumerable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Theory Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## `𝗣𝗔⁻` is `Δ₁` -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## The code of `succInd` as a function of the code of its body -/

section succInd

/-- The code of the substitution vector `![t]`. -/
def substCode {k : ℕ} (t : ArithmeticSemiterm ℕ k) : ℕ :=
  Matrix.vecToNat fun i ↦ Encodable.encode (![t] i)

lemma substCode_eq {k : ℕ} (t : ArithmeticSemiterm ℕ k) :
    substCode t = SemitermVec.val (![⌜t⌝] : SemitermVec ℕ ℒₒᵣ 1 k) := by
  rw [substCode, ← natCast_nat (Matrix.vecToNat _), ← Semiterm.quote_eq_encode' (V := ℕ) ![t]];
  congr 1;
  funext i;
  simp [Matrix.cons_val_fin_one];

noncomputable def indBodyVal (k : V) : V :=
  imp ℒₒᵣ (subst ℒₒᵣ ↑(substCode (‘0’ : ArithmeticSemiterm ℕ 0)) k)
    (imp ℒₒᵣ (qqAll (imp ℒₒᵣ k (subst ℒₒᵣ ↑(substCode (‘#0 + 1’ : ArithmeticSemiterm ℕ 1)) k)))
      (qqAll k))

lemma le_indBodyVal (k : V) : k ≤ indBodyVal k :=
  (le_qqAll _).trans (lt_or_right _ _ |>.trans (lt_or_right _ _)).le

lemma indBodyVal_quote (γ : ArithmeticSemiproposition 1) :
    indBodyVal (⌜γ⌝ : ℕ) = (⌜succInd γ⌝ : ℕ) := by
  have e : (⌜succInd γ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 0) =
      ⌜γ ⇜ ![(‘0’ : ArithmeticSemiterm ℕ 0)]⌝
        🡒 ((∀¹ (⌜γ⌝ 🡒 ⌜γ ⇜ ![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)]⌝)) 🡒 ∀¹ ⌜γ⌝) := by
    unfold succInd;
    rw [show γ ⇜ (![#0] : Fin 1 → ArithmeticSemiterm ℕ 1) = γ by simp];
    simp;
  change _ = (⌜succInd γ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val;
  rw [e];
  simp [indBodyVal, substCode_eq, Matrix.constant_eq_singleton];
  rfl;

noncomputable def indBodyValGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ a, !(substsGraph ℒₒᵣ) a ↑(substCode (‘0’ : ArithmeticSemiterm ℕ 0)) k ∧
    ∃ s1, !(substsGraph ℒₒᵣ) s1 ↑(substCode (‘#0 + 1’ : ArithmeticSemiterm ℕ 1)) k ∧
    ∃ i1, !(impGraph ℒₒᵣ) i1 k s1 ∧
    ∃ qa1, !qqAllDef qa1 i1 ∧
    ∃ qak, !qqAllDef qak k ∧
    ∃ i2, !(impGraph ℒₒᵣ) i2 qa1 qak ∧
    !(impGraph ℒₒᵣ) y a i2”

instance indBodyVal.defined : 𝚺ᴬ₁-Function₁ (indBodyVal : V → V) via indBodyValGraph :=
  .mk fun v ↦ by simp [indBodyValGraph, numeral_eq_natCast, indBodyVal]

end succInd

/-! ## Recognizing the induction schema on codes -/

section InductionR

/-- `InductionR S p` holds when `p` codes `∀¹* β` for a formula `β` without free variables such
that `β`, with its bound variables replaced by free ones, is `succInd ψ` for some `ψ` with `S ⌜ψ⌝`.
-/
def InductionR (S : V → Prop) (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ S K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

noncomputable def chInd (cond : 𝚫ᴬ₁.Semisentence 1) : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(isUFormula ℒₒᵣ).sigma b
      ∧ !(shiftGraph ℒₒᵣ) b b ∧ !(bvGraph ℒₒᵣ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(substsGraph ℒₒᵣ) s fv b
        ∧ ∃ K < s + 1, !(isSemiformula ℒₒᵣ).sigma 1 K
          ∧ !cond.sigma K ∧ !indBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(isUFormula ℒₒᵣ).pi b
      ∧ (∀ y, !(shiftGraph ℒₒᵣ) y b → y = b)
      ∧ (∀ y, !(bvGraph ℒₒᵣ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(substsGraph ℒₒᵣ) s fv b
        → ∃ K < s + 1, !(isSemiformula ℒₒᵣ).pi 1 K
          ∧ !cond.pi K ∧ ∀ ib, !indBodyValGraph ib K → s = ib”)

instance InductionR.defined {S : V → Prop} {cond : 𝚫ᴬ₁.Semisentence 1}
    [hcond : 𝚫ᴬ₁-Predicate[V] S via cond] :
    𝚫ᴬ₁-Predicate[V] (InductionR S : V → Prop) via chInd cond := .mk <| by
  constructor;
  · intro v; simp [chInd, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm];
  · intro v;
    simp [chInd, Bounding.HierarchySymbol.Semiformula.val_sigma, InductionR, lt_succ_iff_le,
      eq_comm];

lemma InductionR.mono {S S' : V → Prop} (hS : ∀ K, S K → S' K) {p : V} (h : InductionR S p) :
    InductionR S' p := by
  obtain ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hKS, hsub⟩ := h;
  exact ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hS K hKS, hsub⟩;

private lemma freeVariables_eq_empty_of_shift {m : ℕ} (β : ArithmeticSemiproposition m)
    (hsh : shift ℒₒᵣ (⌜β⌝ : ℕ) = ⌜β⌝) : β.freeVariables = ∅ := by
  have hsβ : Rewriting.shift β = β :=
    (Semiformula.quote_inj_iff (V := ℕ)).mp <| by rw [Semiformula.quote_shift]; exact hsh;
  by_contra! hne;
  obtain ⟨x, hx, hmin⟩ : ∃ x ∈ β.freeVariables, ∀ y ∈ β.freeVariables, x ≤ y :=
    ⟨_, β.freeVariables.min'_mem hne, fun y hy ↦ β.freeVariables.min'_le y hy⟩;
  rw [← hsβ] at hx;
  rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, hi⟩);
  · simp [Rew.shift_bvar, Semiterm.FVar?] at hi;
  · have : x = z + 1 := by
      simpa [Rew.shift_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi;
    have := hmin z hz;
    omega;

private lemma allClosure_eq_univCl' {m : ℕ} (β : ArithmeticSemiproposition m)
    (hfree : β.freeVariables = ∅) (hbv : bv ℒₒᵣ (⌜β⌝ : ℕ) = m) :
    (∀¹* β : ArithmeticSemiproposition 0)
      = (β ⇜ fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)).univCl' := by
  obtain ⟨χ, hχ⟩ : ∃ χ, β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = χ := ⟨_, rfl⟩;
  rw [hχ];
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
        = Rew.castLE (Nat.le_add_left m 0) ▹ β := by
      rw [← hχ, ← TransitiveRewriting.comp_app];
      apply Semiformula.rew_eq_of_funEqOn;
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff];
      · intro x hx; simp [Semiformula.FVar?, hfree] at hx;
    rw [this, Semiformula.quote_castLE];
  have hfvle : χ.fvSup ≤ m := by
    by_contra! h;
    have hx := Semiformula.fvar?_fvSup_pred χ (by omega);
    rw [← hχ] at hx;
    rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, -⟩);
    · have : χ.fvSup - 1 = i := by
        simpa [hχ, Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi;
      omega;
    · simp [Semiformula.FVar?, hfree] at hz;
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ := by
    have : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
        = Rew.castLE (by omega : 0 + χ.fvSup ≤ 0 + m) ▹ (Rew.fixitr 0 χ.fvSup ▹ χ) := by
      rw [← TransitiveRewriting.comp_app];
      apply Semiformula.rew_eq_of_funEqOn₀;
      intro x hx;
      have := Semiformula.lt_fvSup_of_fvar? hx;
      simp [Rew.comp_app, Rew.fixitr_fvar, this, show x < m by omega];
    rw [this, Semiformula.quote_castLE];
  have hm : m = χ.fvSup := by rw [← hbv, ← hcodeβ, hcode]; exact bv_quote_fixitr χ;
  apply (Semiformula.quote_inj_iff (V := ℕ)).mp;
  rw [quote_allClosure, Semiformula.univCl', quote_allClosure, ← hcodeβ, hcode, hm];
  simp;

lemma inductionR_quote_iff {S : ℕ → Prop} {C : ArithmeticSemiproposition 1 → Prop}
    (hS : ∀ γ, S (⌜γ⌝ : ℕ) ↔ C γ) (φ : ArithmeticSemiproposition 0) :
    InductionR S (⌜φ⌝ : ℕ) ↔ ∃ σ ∈ InductionScheme ℒₒᵣ C, φ = σ := by
  constructor;
  · rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hK, hKS, hsubst⟩;
    obtain ⟨γ, rfl⟩ := IsSemiformula.sound hK;
    obtain ⟨β, rfl⟩ := IsSemiformula.sound (hbv ▸ hU.isSemiformula);
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ :=
      (Semiformula.quote_inj_iff (V := ℕ)).mp <| by
        simpa [hsubst, indBodyVal_quote] using (subst_fvarVec_quote' (V := ℕ) β).symm;
    have hφ : φ = ∀¹* β := (Semiformula.quote_inj_iff (V := ℕ)).mp <| by
      simp [hp, quote_allClosure];
    use (succInd γ).univCl;
    and_intros;
    · exact ⟨γ, (hS γ).mp hKS, rfl⟩;
    · simp [hφ, allClosure_eq_univCl' β (freeVariables_eq_empty_of_shift β hsh) hbv, hβγ];
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩;
    set χ := succInd ψ;
    have hs : subst ℒₒᵣ (fvarVec (0 + χ.fvSup : ℕ))
        (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ : ℕ)
          = indBodyVal (⌜ψ⌝ : ℕ) := by
      simpa [quote_subst_fvar_fixitr, indBodyVal_quote]
        using subst_fvarVec_quote' (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ);
    rw [Semiformula.coe_univCl_eq_univCl', quote_univCl', natCast_nat];
    exact ⟨_, index_le_qqAlls _ _, _, le_qqAlls _ _, rfl,
      (Semiformula.quote_isSemiformula _).isUFormula, quote_shift_fixitr χ,
      (bv_quote_fixitr χ).trans (zero_add _).symm, ⌜ψ⌝, by rw [hs]; exact le_indBodyVal _,
      by simp, (hS ψ).mpr hψ, hs⟩;

end InductionR

/-! ## `Δ₁` and r.e. presentations -/

section presentation

/-- `InductionScheme ℒₒᵣ C` is `Δ₁` once `C` is recognized on codes by a `Δ₁`-predicate `S`. -/
noncomputable abbrev InductionScheme.delta1_of {C : ArithmeticSemiproposition 1 → Prop}
    {cond : 𝚫ᴬ₁.Semisentence 1} {S : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V → Prop}
    (hS : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], 𝚫ᴬ₁-Predicate[V] S V via cond)
    (hC : ∀ γ, S ℕ ⌜γ⌝ ↔ C γ) : (InductionScheme ℒₒᵣ C).Δ₁ where
  ch := chInd cond
  mem_iff φ := by
    have := hS ℕ;
    simpa using inductionR_quote_iff hC φ;
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      fun V _ _ ↦ (InductionR.defined (hcond := hS V)).proper

noncomputable instance InductionScheme.delta1_univ : (InductionScheme ℒₒᵣ Set.univ).Δ₁ :=
  InductionScheme.delta1_of (cond := ⊤) (S := fun _ _ _ _ ↦ True)
    (fun _ _ _ ↦ ⟨by simp, by intro v; simp⟩) fun _ ↦ Iff.rfl

noncomputable instance InductionScheme.delta1_hierarchy (Γ : Polarity) (s : ℕ) :
    (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)).Δ₁ :=
  InductionScheme.delta1_of (fun _ _ _ ↦ IsHierarchy.defined Γ s) isHierarchy_quote_iff_s

noncomputable instance InductionScheme.delta1_strictHierarchy (Γ : Polarity) (s : ℕ) :
    (InductionScheme ℒₒᵣ (StrictHierarchy Γ s)).Δ₁ :=
  InductionScheme.delta1_of (fun _ _ _ ↦ IsStrictHierarchy.defined Γ s)
    isStrictHierarchy_quote_iff_s

variable {Γ : Polarity} {s : ℕ} {p : V}

lemma Peano.mem_Δ₁Class_iff :
    p ∈ 𝗣𝗔.Δ₁Class ↔ p ∈ 𝗣𝗔⁻.Δ₁Class ∨ InductionR (fun _ ↦ True) p :=
  Δ₁Class.mem_union.trans <| .or .rfl <|
    (InductionR.defined (hcond := ⟨by simp, fun _ ↦ by simp⟩)).df ![p]

lemma InductionOnBroadHierarchy.mem_Δ₁Class_iff :
    p ∈ (𝗜𝗡𝗗⁺ Γ s).Δ₁Class ↔ p ∈ 𝗣𝗔⁻.Δ₁Class ∨ InductionR (IsHierarchy Γ s) p :=
  Δ₁Class.mem_union.trans <| .or .rfl <| InductionR.defined.df ![p]

lemma InductionOnHierarchy.mem_Δ₁Class_iff :
    p ∈ (𝗜𝗡𝗗 Γ s).Δ₁Class ↔ p ∈ 𝗣𝗔⁻.Δ₁Class ∨ InductionR (IsStrictHierarchy Γ s) p :=
  Δ₁Class.mem_union.trans <| .or .rfl <| InductionR.defined.df ![p]

lemma _root_.FFL.FirstOrder.Theory.RE.of_delta1 (T : ArithmeticTheory) [T.Δ₁] : T.RE := ⟨by
  have h : REPred (· ∈ T.Δ₁Class (V := ℕ)) :=
    rePred_iff_sigma1.mpr <| Bounding.HierarchySymbol.Definable.of_deltaOne Δ₁Class.definable
  exact (h.comp Computable.encode).of_eq fun σ ↦ by simp [← Sentence.quote_eq_encode_nat]⟩

instance : (InductionScheme ℒₒᵣ Set.univ).RE := .of_delta1 _

instance (Γ : Polarity) (s : ℕ) : (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)).RE :=
  .of_delta1 _

instance : 𝗣𝗔.RE := .of_delta1 _

instance (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗⁺ Γ s).RE := .of_delta1 _

end presentation

end FFL.FirstOrder.Arithmetic
