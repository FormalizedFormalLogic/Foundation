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

open FFL.FirstOrder.Theory

/-! ## `𝗣𝗔⁻` is `Δ₁` -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## Typed decomposition of `succInd` -/

section succInd

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma succInd_eq (φ : ArithmeticSemiproposition 1) :
    succInd φ =
      ((φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0))
        🡒 ((∀¹ (φ 🡒 (φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)))) 🡒 ∀¹ φ)) := by
  unfold succInd; simp

lemma typed_quote_succInd (φ : ArithmeticSemiproposition 1) :
    (⌜succInd φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0) =
      (⌜φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0)⌝)
        🡒 ((∀¹ (⌜φ⌝ 🡒 ⌜φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)⌝)) 🡒 ∀¹ ⌜φ⌝) := by
  unfold succInd
  rw [show φ ⇜ (![#0] : Fin 1 → ArithmeticSemiterm ℕ 1) = φ from by simp]
  simp

/-- The typed `succInd` shape as a function of the (typed) core code `K = ⌜ψ⌝`. -/
noncomputable def indBody (K : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Semiformula V ℒₒᵣ 0 :=
  (K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    🡒 ((∀¹ (K 🡒 K.subst ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) 🡒 ∀¹ K)

lemma indBody_quote (φ : ArithmeticSemiproposition 1) :
    indBody (⌜φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  rw [typed_quote_succInd]; unfold indBody; simp [Matrix.constant_eq_singleton]

/-- The raw `V → V` form of `(indBody ·).val`. -/
noncomputable def indBodyVal (k : V) : V :=
  Bootstrapping.imp ℒₒᵣ
    (Bootstrapping.subst ℒₒᵣ
      (Bootstrapping.SemitermVec.val
        (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 0)) k)
    (Bootstrapping.imp ℒₒᵣ
      (Bootstrapping.qqAll (Bootstrapping.imp ℒₒᵣ k
        (Bootstrapping.subst ℒₒᵣ
          (Bootstrapping.SemitermVec.val
            (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 1)) k)))
      (Bootstrapping.qqAll k))

lemma indBodyVal_eq (K : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    indBodyVal K.val = (indBody K).val := by
  simp only [indBodyVal, indBody, Bootstrapping.Semiformula.val_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_substs]

lemma le_indBodyVal (k : V) : k ≤ indBodyVal k := by
  unfold indBodyVal Bootstrapping.imp
  exact (Bootstrapping.le_qqAll _).trans
    (le_of_lt ((Bootstrapping.lt_or_right _ _).trans (Bootstrapping.lt_or_right _ _)))

lemma indBodyVal_quote (γ : ArithmeticSemiproposition 1) :
    indBodyVal (⌜γ⌝ : ℕ) = (⌜succInd γ⌝ : ℕ) := by
  rw [show (⌜γ⌝ : ℕ) = (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl, indBodyVal_eq,
    indBody_quote]
  rfl

instance indBodyVal_definable : 𝚺ᴬ₁-Function₁ (indBodyVal : V → V) := by
  unfold indBodyVal
  definability

/-! ### A concrete `𝚺ᴬ₁`-graph for `indBodyVal` -/

/-- Standard `ℕ`-code of the substitution vector `![⌜‘0’⌝]` (the `ψ(0)` instance). -/
def indSubstConst0 : ℕ :=
  Matrix.vecToNat fun i : Fin 1 ↦ Encodable.encode ((![(‘0’ : ArithmeticSemiterm ℕ 0)]) i)

/-- Standard `ℕ`-code of the substitution vector `![⌜‘#0+1’⌝]` (the `ψ(x+1)` instance). -/
def indSubstConst1 : ℕ :=
  Matrix.vecToNat fun i : Fin 1 ↦ Encodable.encode ((![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)]) i)

lemma val_indSubstConst0 :
    (↑indSubstConst0 : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 0) := by
  rw [indSubstConst0,
    ← FFL.FirstOrder.Semiterm.quote_eq_encode' (V := V) (![(‘0’ : ArithmeticSemiterm ℕ 0)])]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

lemma val_indSubstConst1 :
    (↑indSubstConst1 : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 1) := by
  rw [indSubstConst1,
    ← FFL.FirstOrder.Semiterm.quote_eq_encode' (V := V) (![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)])]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

/-- Concrete `𝚺ᴬ₁`-graph of `indBodyVal`, a chain of the `subst`/`imp`/`qqAll` graphs. -/
noncomputable def indBodyValGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ a, !(Bootstrapping.substsGraph ℒₒᵣ) a ↑indSubstConst0 k ∧
    ∃ s1, !(Bootstrapping.substsGraph ℒₒᵣ) s1 ↑indSubstConst1 k ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₒᵣ) i1 k s1 ∧
    ∃ qa1, !qqAllDef qa1 i1 ∧
    ∃ qak, !qqAllDef qak k ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₒᵣ) i2 qa1 qak ∧
    !(Bootstrapping.impGraph ℒₒᵣ) y a i2”

instance indBodyVal.defined :
    𝚺ᴬ₁-Function₁ (indBodyVal : V → V) via indBodyValGraph := .mk fun v ↦ by
  simp [indBodyValGraph, numeral_eq_natCast, val_indSubstConst0, val_indSubstConst1, indBodyVal]

end succInd

/-! ## The induction schema is `Δ₁` -/

section ch

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

/-- The recognizer predicate for `InductionScheme ℒₒᵣ C` over a model `V`, parameterized by a side
condition `S` on the recovered core. -/
def InductionR (S : V → Prop) (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ S K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

end ch

/-- Concrete `𝚫ᴬ₁.Semisentence 1` recognizer for `InductionR cond`. -/
noncomputable def chInd (cond : 𝚫ᴬ₁.Semisentence 1) : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₒᵣ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₒᵣ) b b ∧ !(Bootstrapping.bvGraph ℒₒᵣ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).sigma 1 K
          ∧ !cond.sigma K ∧ !indBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₒᵣ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₒᵣ) y b → y = b)
      ∧ (∀ y, !(Bootstrapping.bvGraph ℒₒᵣ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).pi 1 K
          ∧ !cond.pi K ∧ ∀ ib, !indBodyValGraph ib K → s = ib”)

noncomputable def chUniv : 𝚫ᴬ₁.Semisentence 1 := chInd ⊤

section chDefined

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

instance InductionR.defined {S : V → Prop} {cond : 𝚫ᴬ₁.Semisentence 1}
    [hcond : 𝚫ᴬ₁-Predicate[V] S via cond] :
    𝚫ᴬ₁-Predicate[V] (InductionR S : V → Prop) via chInd cond := .mk <| by
  constructor
  · intro v; simp [chInd, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chInd, Bounding.HierarchySymbol.Semiformula.val_sigma, InductionR, lt_succ_iff_le,
      eq_comm]

noncomputable instance InductionR.univ_defined :
    𝚫ᴬ₁-Predicate[V] (InductionR (fun _ ↦ True) : V → Prop) via chUniv :=
  InductionR.defined (hcond := ⟨by simp, by intro v; simp⟩)

noncomputable instance InductionR.hierarchy_defined (Γ : Polarity) (s : ℕ) :
    𝚫ᴬ₁-Predicate[V] (InductionR (IsHierarchy Γ s) : V → Prop) via chInd (isHierarchy Γ s) :=
  InductionR.defined

end chDefined

lemma mem_inductionScheme_iff {C : ArithmeticSemiproposition 1 → Prop}
    (φ : ArithmeticSemiproposition 0) :
    (∃ σ ∈ InductionScheme ℒₒᵣ C, φ = (σ : ArithmeticSemiproposition 0))
      ↔ ∃ ψ : ArithmeticSemiproposition 1, C ψ ∧ φ = (succInd ψ).univCl' := by
  simp only [InductionScheme, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, by simp [Semiformula.coe_univCl_eq_univCl']⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨Semiformula.univCl (succInd ψ), ⟨ψ, hψ, rfl⟩,
      by simp [Semiformula.coe_univCl_eq_univCl']⟩

/-- A freevar-free, `bv`-pinned formula `β` that substitutes back to `succInd γ` is exactly the
`fixitr`-image, so its `m`-fold closure equals `(succInd γ).univCl'`. -/
theorem closure_inversion {m : ℕ} (β : ArithmeticSemiproposition m)
    (γ : ArithmeticSemiproposition 1)
    (hfree : β.freeVariables = ∅) (hbv : Bootstrapping.bv (V := ℕ) ℒₒᵣ (⌜β⌝ : ℕ) = m)
    (hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ) :
    (∀¹* β : ArithmeticSemiproposition 0) = (succInd γ).univCl' := by
  set χ : ArithmeticSemiproposition 0 := succInd γ with hχ
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have hcompcast :
        ((Rew.fixitr 0 m).comp (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))) ▹ β
          = (Rew.castLE (Nat.le_add_left m 0) ▹ β : ArithmeticSemiproposition (0 + m)) := by
      apply Semiformula.rew_eq_of_funEqOn
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff]
      · intro x hx; rw [Semiformula.FVar?, hfree] at hx; simp at hx
    have heq : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
        = (Rew.castLE (Nat.le_add_left m 0) ▹ β : ArithmeticSemiproposition (0 + m)) := by
      rw [← hcompcast, TransitiveRewriting.comp_app,
        show (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) ▹ β) = χ from hβγ]
    rw [heq, Semiformula.quote_castLE (V := ℕ) β (Nat.le_add_left m 0)]
  have hfvbound : ∀ x, χ.FVar? x → x < m := by
    intro x hx
    rw [show χ = β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) from hβγ.symm] at hx
    rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, _⟩)
    · have : x = (↑i : ℕ) := by
        simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
      rw [this]; exact i.isLt
    · rw [Semiformula.FVar?, hfree] at hz; simp at hz
  have hfvle : χ.fvSup ≤ m := by
    rcases Nat.eq_zero_or_pos χ.fvSup with h0 | hpos
    · omega
    · have := hfvbound (χ.fvSup - 1) (Semiformula.fvar?_fvSup_pred χ hpos); omega
  have hcast_eq : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
      = (Rew.castLE (by omega : (0 + χ.fvSup) ≤ (0 + m))
          ▹ (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))) := by
    rw [← TransitiveRewriting.comp_app]
    apply Semiformula.rew_eq_of_funEqOn₀
    intro x hx
    have hxlt : x < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hx
    simp [Rew.comp_app, Rew.fixitr_fvar, hxlt, show x < m from by omega]
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ := by
    rw [hcast_eq, Semiformula.quote_castLE (V := ℕ)
      (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup)) (by omega)]
  have hm : m = χ.fvSup := by
    rw [← hbv, ← hcodeβ, hcode]; exact Bootstrapping.bv_quote_fixitr χ
  apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
  rw [Bootstrapping.quote_allClosure (V := ℕ) β, Semiformula.univCl',
    Bootstrapping.quote_allClosure (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), ← hcodeβ, hcode, hm]
  simp

private lemma freeVariables_eq_empty_of_shift_quote_fixed {m : ℕ} (β : ArithmeticSemiproposition m)
    (hsh : Bootstrapping.shift (V := ℕ) ℒₒᵣ (⌜β⌝ : ℕ) = ⌜β⌝) : β.freeVariables = ∅ := by
  have hsβ : Rewriting.shift β = β :=
    (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      (by rw [Semiformula.quote_shift (V := ℕ) β]; exact hsh)
  have step : ∀ x, β.FVar? x → 1 ≤ x ∧ β.FVar? (x - 1) := by
    intro x hx
    rw [← hsβ] at hx
    rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, hi⟩)
    · simp [Rew.shift_bvar, Semiterm.FVar?] at hi
    · have hxz : x = z + 1 := by
        simpa [Rew.shift_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
      exact ⟨by omega, by rw [hxz]; simpa using hz⟩
  by_contra hne
  classical
  have hnem := Finset.nonempty_of_ne_empty hne
  obtain ⟨hge, hpred⟩ := step (β.freeVariables.min' hnem) (β.freeVariables.min'_mem hnem)
  exact absurd (β.freeVariables.min'_le _ hpred) (by omega)

/-- `InductionR S` fires exactly on codes of universal closures of `succInd ψ` for `ψ` with `C ψ`,
given that `S` correctly recognizes the codes of `C`-formulas. -/
theorem inductionR_quote_iff {S : ℕ → Prop} {C : ArithmeticSemiproposition 1 → Prop}
    (hS : ∀ γ, S (⌜γ⌝ : ℕ) ↔ C γ) (φ : ArithmeticSemiproposition 0) :
    InductionR S (⌜φ⌝ : ℕ) ↔ ∃ ψ, C ψ ∧ φ = (succInd ψ).univCl' := by
  constructor
  · rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hKsemi, hKS, hsubst⟩
    obtain ⟨γ, rfl⟩ := Bootstrapping.IsSemiformula.sound hKsemi
    have hbsemi : Bootstrapping.IsSemiformula ℒₒᵣ m b := hbv ▸ hU.isSemiformula
    obtain ⟨β, rfl⟩ := Bootstrapping.IsSemiformula.sound hbsemi
    refine ⟨γ, (hS γ).mp hKS, ?_⟩
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      have e := Bootstrapping.subst_fvarVec_quote' (V := ℕ) β
      simp only [natCast_nat] at e
      rw [← e, hsubst, indBodyVal_quote]
    have hβfree : β.freeVariables = ∅ := freeVariables_eq_empty_of_shift_quote_fixed β hsh
    have hφ : φ = (∀¹* β : ArithmeticSemiproposition 0) := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      rw [hp, Bootstrapping.quote_allClosure (V := ℕ) β]; simp
    rw [hφ]
    exact closure_inversion β γ hβfree hbv hβγ
  · rintro ⟨ψ, hψ, rfl⟩
    set χ : ArithmeticSemiproposition 0 := succInd ψ with hχ
    set b : ℕ :=
      (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ : ℕ) with hb
    have hcode : (⌜χ.univCl'⌝ : ℕ) = Bootstrapping.qqAlls b ((0 + χ.fvSup : ℕ)) := by
      rw [hb, Bootstrapping.quote_univCl' (V := ℕ) χ]; simp
    have hs : Bootstrapping.subst ℒₒᵣ (Bootstrapping.fvarVec (0 + χ.fvSup : ℕ)) b
        = indBodyVal (⌜ψ⌝ : ℕ) := by
      rw [hb]
      have hsub := Bootstrapping.subst_fvarVec_quote' (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))
      simp only [natCast_nat] at hsub
      rw [hsub, Bootstrapping.quote_subst_fvar_fixitr χ,
        show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl,
        indBodyVal_eq, indBody_quote, hχ]
      rfl
    refine ⟨(0 + χ.fvSup : ℕ), ?_, b, ?_, ?_, ?_, ?_, ?_, (⌜ψ⌝ : ℕ), ?_, ?_, ?_, ?_⟩
    · rw [hcode]; exact Bootstrapping.index_le_qqAlls _ _
    · rw [hcode]; exact Bootstrapping.le_qqAlls _ _
    · exact hcode
    · rw [hb]
      exact (Semiformula.quote_isSemiformula (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))).isUFormula
    · rw [hb]; exact Bootstrapping.quote_shift_fixitr χ
    · rw [hb]; exact (Bootstrapping.bv_quote_fixitr χ).trans (zero_add _).symm
    · rw [hs]; exact le_indBodyVal _
    · simp
    · exact (hS ψ).mpr hψ
    · exact hs

/-- The induction schema `InductionScheme ℒₒᵣ Set.univ` is `Δ₁`, via the recognizer `chUniv`. -/
noncomputable instance InductionScheme.delta1_univ :
    (InductionScheme ℒₒᵣ Set.univ).Δ₁ where
  ch := chUniv
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] chUniv.val) ↔ InductionR (fun _ ↦ True) (⌜φ⌝ : ℕ) := by
      simp
    rw [h]
    exact (inductionR_quote_iff (C := Set.univ) (fun _ ↦ Iff.rfl) φ).trans
      (mem_inductionScheme_iff φ).symm
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      (fun V _ _ ↦ by
        have := InductionR.univ_defined (V := V); simp)

/-- The induction schema over `ℬ[<, ℒₒᵣ].Hierarchy Γ s` is `Δ₁`. -/
noncomputable instance InductionScheme.delta1_hierarchy (Γ : Polarity) (s : ℕ) :
    (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)).Δ₁ where
  ch := chInd (Bootstrapping.isHierarchy Γ s)
  mem_iff φ := by
    simpa using (inductionR_quote_iff (isHierarchy_quote_iff_s (V := ℕ)) φ).trans
      (mem_inductionScheme_iff φ).symm;
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      fun V _ _ ↦ by have := InductionR.hierarchy_defined (V := V) Γ s; simp

noncomputable instance InductionOnBroadHierarchy.delta1 (Γ : Polarity) (s : ℕ) :
    (𝗜𝗡𝗗⁺ Γ s).Δ₁ :=
  Δ₁.add PeanoMinus.delta1 inferInstance

/-! ## The strict induction theories are `Δ₁` -/

open Bootstrapping in
noncomputable instance InductionScheme.delta1_strictHierarchy :
    (Γ : Polarity) → (s : ℕ) → (InductionScheme ℒₒᵣ (StrictHierarchy Γ s)).Δ₁
  | 𝚺, s =>
    { ch := chInd (isStrictSigma s)
      mem_iff φ := by
        simpa using
          (inductionR_quote_iff isStrictSigma_quote_iff_s φ).trans (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }
  | 𝚷, s =>
    { ch := chInd (isStrictPi s)
      mem_iff φ := by
        simpa using
          (inductionR_quote_iff isStrictPi_quote_iff_s φ).trans (mem_inductionScheme_iff φ).symm;
      isDelta1 :=
        Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
          fun _ _ _ ↦ by simp }

noncomputable instance InductionOnHierarchy.delta1 (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗 Γ s).Δ₁ :=
  Δ₁.add PeanoMinus.delta1 inferInstance

/-! ## `𝗣𝗔` and `𝗜𝗡𝗗⁺ Γ s` are recursively enumerable -/

lemma inductionScheme_re_univ : REPred (· ∈ InductionScheme ℒₒᵣ Set.univ) := by
  have hR : REPred (InductionR fun _ : ℕ ↦ True) := rePred_iff_sigma1.mpr (by definability)
  refine (hR.comp Computable.encode).of_eq <| fun σ ↦ ?_;
  simpa [Semiformula.quote_eq_encode] using
    (inductionR_quote_iff (S := fun _ : ℕ ↦ True) (C := Set.univ)
      (fun _ ↦ Iff.rfl) σ).trans (mem_inductionScheme_iff σ).symm

lemma inductionScheme_re_hierarchy (Γ : Polarity) (s : ℕ) :
    REPred (· ∈ InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)) := by
  have hR : REPred (InductionR (Bootstrapping.IsHierarchy Γ s)) :=
    rePred_iff_sigma1.mpr <| Bounding.HierarchySymbol.Definable.of_deltaOne
      (InductionR.hierarchy_defined Γ s).to_definable
  refine (hR.comp Computable.encode).of_eq fun σ ↦ ?_;
  simpa [Semiformula.quote_eq_encode] using
    (inductionR_quote_iff (isHierarchy_quote_iff_s (V := ℕ)) σ).trans
      (mem_inductionScheme_iff σ).symm

instance : (InductionScheme ℒₒᵣ Set.univ).RE := ⟨inductionScheme_re_univ⟩

instance (Γ : Polarity) (s : ℕ) : (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)).RE :=
  ⟨inductionScheme_re_hierarchy Γ s⟩

instance : 𝗣𝗔.RE := Theory.RE.add (Theory.RE.ofFinite PeanoMinus.finite) inferInstance

instance (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗⁺ Γ s).RE :=
  Theory.RE.add (Theory.RE.ofFinite PeanoMinus.finite) inferInstance

/-! ## `𝗣𝗔` is `Δ₁`

TODO: remove. Not mathematically essential — `RE` above already suffices. -/

noncomputable instance : 𝗣𝗔.Δ₁ := Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_univ

end FFL.FirstOrder.Arithmetic
