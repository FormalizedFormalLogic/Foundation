module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k : ℕ}

namespace Bootstrapping.Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Bootstrapping.Arithmetic`).
set_option linter.dupNamespace false

noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ

lemma substNumeral_app_quote (σ π : ArithmeticSemisentence 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[⌜π⌝] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁]

lemma substNumeral_app_natCast (σ : ArithmeticSemisentence 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[↑n] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁];

noncomputable def substNumerals (φ : V) (v : Fin k → V) : V :=
  subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ

lemma substNumerals_app_quote (σ : ArithmeticSemisentence k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝ := by
  simp [substNumerals, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb]
  rfl

lemma substNumerals_app_quote_quote
    (σ : ArithmeticSemisentence k) (π : Fin k → ArithmeticSemisentence k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) =
      ⌜((Rew.subst (fun i ↦ ⌜π i⌝)) ▹ σ : ArithmeticSentence)⌝ := by
  simpa [Sentence.coe_quote_eq_quote] using substNumerals_app_quote (V := V) σ (fun i ↦ ⌜π i⌝)

noncomputable def substNumeralParams (k : ℕ) (φ x : V) : V :=
  subst ℒₒᵣ (matrixToVec (numeral x :> fun i : Fin k ↦ qqBvar i)) φ

lemma substNumeralParams_app_quote (σ τ : ArithmeticSemisentence (k + 1)) :
    (substNumeralParams k ⌜σ⌝ ⌜τ⌝ : V) =
      ⌜((Rew.subst (⌜τ⌝ :> fun i : Fin k ↦ #i)) ▹ σ : ArithmeticSemisentence k)⌝ := by
  simp [substNumeralParams, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb, Matrix.vecHead]
  rfl

section

noncomputable def ssnum : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ n, !numeralGraph n x ∧ ∃ v, !adjoinDef v n 0 ∧ !(substsGraph ℒₒᵣ) y v φ”

instance substNumeral.defined : 𝚺ᴬ₁-Function₂ (substNumeral : V → V → V) via ssnum :=
  .mk fun v ↦ by simp [ssnum, substNumeral]

instance substNumeral.definable : 𝚺ᴬ₁-Function₂ (substNumeral : V → V → V) :=
  substNumeral.defined.to_definable

attribute [irreducible] ssnum

noncomputable def ssnums : 𝚺ᴬ₁.Semisentence (k + 2) := .mkSigma
  “y φ. ∃ n, !lenDef ↑k n ∧
    (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k).val ∧ !numeralGraph z #i.succ.succ.succ.succ) ∧
    !(substsGraph ℒₒᵣ) y n φ”

instance substNumerals.defined :
    Bounding.HierarchySymbol.DefinedFunction
      (fun v ↦ substNumerals (v 0) (v ·.succ) : (Fin (k + 1) → V) → V) ssnums := .mk fun v ↦ by
  unfold ssnums
  symm
  suffices
      v 0 = subst ℒₒᵣ (matrixToVec fun i ↦ numeral (v i.succ.succ)) (v 1) ↔
      ∃ x, ↑k = len x ∧ (∀ i : Fin k, x.[↑↑i] = numeral (v i.succ.succ)) ∧
        v 0 = subst ℒₒᵣ x (v 1) by
    simpa [ssnums, substNumerals, numeral_eq_natCast]
  constructor
  · intro h
    refine ⟨matrixToVec fun i ↦ numeral (v i.succ.succ), ?_⟩
    simpa
  · rintro ⟨x, hx, h, e⟩
    suffices (matrixToVec fun i ↦ numeral (v i.succ.succ)) = x by simpa [this]
    apply nth_ext' (k : V)
    · simp
    · simp [hx]
    · intro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simp [h]

attribute [irreducible] ssnums

noncomputable def ssnumParams (k : ℕ) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ v, !lenDef ↑(k + 1) v ∧
    (∃ z, !nthDef z v 0 ∧ !numeralGraph z x) ∧
    (⋀ i, ∃ z, !nthDef z v ↑(i : Fin k).val.succ ∧ !qqBvarDef z ↑i) ∧
    !(substsGraph ℒₒᵣ) y v φ”

instance ssnumParams.defined :
    𝚺ᴬ₁-Function₂[V] substNumeralParams k via ssnumParams k := .mk fun v ↦ by
  symm
  unfold ssnumParams
  suffices
      v 0 = subst ℒₒᵣ (numeral (v 2) ∷ matrixToVec fun i ↦ ^#↑i) (v 1) ↔
      ∃ x, ↑(k + 1) = len x ∧ x.[0] = numeral (v 2) ∧ (∀ (i : Fin k), x.[↑i + 1] = ^#↑i) ∧
        v 0 = subst ℒₒᵣ x (v 1) by
    simpa [ssnumParams, substNumeralParams, numeral_eq_natCast]
  constructor
  · intro h
    use numeral (v 2) ∷ matrixToVec fun i : Fin k ↦ ^#↑i
    simpa
  · rintro ⟨w, wlen, h0, hsucc, he⟩
    suffices (numeral (v 2) ∷ matrixToVec fun i : Fin k ↦ ^#↑i) = w by simp [this, he]
    apply nth_ext' ((k + 1 : ℕ) : V) (by simp) wlen.symm
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [h0]
    · have hi : i < ↑k := by simpa using hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simp [hsucc]

end

section substNumeralItr

namespace SubstNumeralItr

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y p a. y = a”
  succ := .mkSigma
    “y ih n p a. ∃ m, !numeralGraph m ih ∧ ∃ v, !adjoinDef v m 0 ∧ !(substsGraph ℒₒᵣ) y v p”

noncomputable def construction : PR.Construction V blueprint where
  zero v := v 1
  succ v _ ih := substNumeral (v 0) ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, substNumeral]

end SubstNumeralItr

open SubstNumeralItr

noncomputable def substNumeralItr (p a k : V) : V := construction.result ![p, a] k

@[simp] lemma substNumeralItr_zero (p a : V) : substNumeralItr p a 0 = a := by
  simp [substNumeralItr, construction]

@[simp] lemma substNumeralItr_succ (p a k : V) :
    substNumeralItr p a (k + 1) = substNumeral p (substNumeralItr p a k) := by
  simp [substNumeralItr, construction]

noncomputable def _root_.FFL.FirstOrder.Arithmetic.substNumeralItrDef : 𝚺ᴬ₁.Semisentence 4 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance substNumeralItr.defined :
    𝚺ᴬ₁-Function₃[V] substNumeralItr via substNumeralItrDef := .mk fun v ↦ by
  simp [construction.result_defined_iff, substNumeralItrDef, substNumeralItr]

instance substNumeralItr.definable : 𝚺ᴬ₁-Function₃ (substNumeralItr : V → V → V → V) :=
  substNumeralItr.defined.to_definable

lemma substNumeralItr_quote (σ : ArithmeticSemisentence 1) (π : ArithmeticSentence) (k : ℕ) :
    substNumeralItr (⌜σ⌝ : V) ⌜π⌝ (k : V) =
      ⌜(fun π : ArithmeticSentence ↦ (σ/[⌜π⌝] : ArithmeticSentence))^[k] π⌝ := by
  induction k with
  | zero => simp;
  | succ k ih =>
    rw [Nat.cast_succ, substNumeralItr_succ, ih, Function.iterate_succ_apply'];
    simpa [Sentence.coe_quote_eq_quote] using substNumeral_app_natCast (V := V) σ
      ⌜(fun π : ArithmeticSentence ↦ (σ/[⌜π⌝] : ArithmeticSentence))^[k] π⌝

end substNumeralItr

end Bootstrapping.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]

section Diagonalization

noncomputable def diag (θ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
  “x. ∀ y, !ssnum y x x → !θ y”

noncomputable def fixedpoint (θ : ArithmeticSemisentence 1) : ArithmeticSentence :=
  (diag θ)/[⌜diag θ⌝]

theorem diagonal (θ : ArithmeticSemisentence 1) :
    T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝] :=
  haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  complete.{0} T _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices V ⊧/![] (fixedpoint θ) ↔ V ⊧/![⌜fixedpoint θ⌝] θ by
      simpa [models_iff, Matrix.constant_eq_singleton]
    let t : V := ⌜diag θ⌝
    have ht : substNumeral t t = ⌜fixedpoint θ⌝ := by
      simp [t, fixedpoint, substNumeral_app_quote]
    calc
      V ⊧/![] (fixedpoint θ)
    _ ↔ V ⊧/![t] (diag θ)         := by simp [fixedpoint, t]
    _ ↔ V ⊧/![substNumeral t t] θ := by simp [diag]
    _ ↔ V ⊧/![⌜fixedpoint θ⌝] θ   := by simp [ht]

end Diagonalization

section Multidiagonalization

variable {i j : Fin k} {m : ℕ}

/-- $\mathrm{diag}_i(\vec{x}) := (\forall \vec{y})\left[ \left(\bigwedge_j \mathrm{ssnums}(y_j, x_j,
\vec{x})\right) \to \theta_i(\vec{y}) \right]$ -/
noncomputable def multidiag (θ : ArithmeticSemisentence k) : ArithmeticSemisentence k :=
  ∀¹^[k] (
    (Matrix.conj fun j : Fin k ↦
      (Rew.subst <| #(j.addCast k) :> #(j.addNat k) :> fun l ↦ #(l.addNat k)) ▹ ssnums.val) 🡒
    (Rew.subst fun j ↦ #(j.addCast k)) ▹ θ)

noncomputable def multifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k) :
    ArithmeticSentence :=
  (Rew.subst fun j ↦ ⌜multidiag (θ j)⌝) ▹ (multidiag (θ i))

theorem multidiagonal (θ : Fin k → ArithmeticSemisentence k) :
    T ⊢ multifixedpoint θ i 🡘 (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i) :=
  haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans inferInstance (inferInstance : 𝗜𝚺₁ ⪯ T)
  complete.{0} T _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices V ⊧/![] (multifixedpoint θ i) ↔ V ⊧/(fun i ↦ ⌜multifixedpoint θ i⌝) (θ i) by
      simpa [models_iff, Function.comp_def, Matrix.empty_eq]
    let t : Fin k → V := fun i ↦ ⌜multidiag (θ i)⌝
    have ht : ∀ i, substNumerals (t i) t = ⌜multifixedpoint θ i⌝ := by
      intro i; simp [t, multifixedpoint, substNumerals_app_quote_quote]
    calc
      V ⊧/![] (multifixedpoint θ i)
        ↔ V ⊧/t (multidiag (θ i))                   := by
          simp [t, multifixedpoint, Function.comp_def]
      _ ↔ V ⊧/(fun i ↦ substNumerals (t i) t) (θ i) := by
          simp [multidiag, ← funext_iff, Function.comp_def]
      _ ↔ V ⊧/(fun i ↦ ⌜multifixedpoint θ i⌝) (θ i) := by simp [ht]

noncomputable def exclusiveMultifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k) :
    ArithmeticSentence :=
  multifixedpoint (fun j ↦ (θ j).padding j) i

@[simp] lemma exclusiveMultifixedpoint_inj_iff (θ : Fin k → ArithmeticSemisentence k) :
    exclusiveMultifixedpoint θ i = exclusiveMultifixedpoint θ j ↔ i = j := by
  constructor
  · unfold exclusiveMultifixedpoint multifixedpoint
    suffices ∀ ω : Rew ℒₒᵣ Empty k Empty 0,
        ω ▹ multidiag ((θ i).padding i) = ω ▹ multidiag ((θ j).padding j) → i = j by
      exact this _
    intro
    simp [multidiag, Fin.val_inj]
  · rintro rfl; rfl

theorem exclusiveMultidiagonal (θ : Fin k → ArithmeticSemisentence k) :
    T ⊢ exclusiveMultifixedpoint θ i 🡘
      (Rew.subst fun j ↦ ⌜exclusiveMultifixedpoint θ j⌝) ▹ θ i := by
  have : T ⊢ exclusiveMultifixedpoint θ i 🡘
      ((Rew.subst fun j ↦ ⌜exclusiveMultifixedpoint θ j⌝) ▹ θ i).padding ↑i := by
    simpa using! multidiagonal (T := T) (fun j ↦ (θ j).padding j) (i := i)
  exact Entailment.E_trans this (Entailment.padding_iff _ _)

lemma multifixedpoint_pi
    {θ : Fin k → ArithmeticSemisentence k} (h : ∀ i, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (θ i)) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (multifixedpoint θ i) := by
  simpa [multifixedpoint, multidiag, h] using fun _ ↦
    Bounding.Hierarchy.mono (ℬ := ℬ[<, ℒₒᵣ]) (s := 1) (by simp) (by simp)

lemma exclusiveMultifixedpoint_pi
    {θ : Fin k → ArithmeticSemisentence k} (h : ∀ i, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (θ i)) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (exclusiveMultifixedpoint θ i) := by
  apply multifixedpoint_pi; simp [h]

end Multidiagonalization

section ParameterizedDiagonalization

noncomputable def parameterizedDiag (θ : ArithmeticSemisentence (k + 1)) :
    ArithmeticSemisentence (k + 1) :=
  “x. ∀ y, !(ssnumParams k) y x x → !θ y ⋯”

noncomputable def parameterizedFixedpoint (θ : ArithmeticSemisentence (k + 1)) :
    ArithmeticSemisentence k :=
  (Rew.subst (⌜parameterizedDiag θ⌝ :> fun j ↦ #j)) ▹ parameterizedDiag θ

theorem parameterized_diagonal (θ : ArithmeticSemisentence (k + 1)) :
    T ⊢ ∀¹* (parameterizedFixedpoint θ 🡘 “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”) :=
  haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  complete.{0} T _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices
        ∀ params : Fin k → V,
          V ⊧/params (parameterizedFixedpoint θ) ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ by
      simpa [models_iff, Matrix.comp_vecCons', BinderNotation.finSuccItr, Function.comp_def,
        Matrix.empty_eq]
    intro params
    let t : V := ⌜parameterizedDiag θ⌝
    have ht : substNumeralParams k t t = ⌜parameterizedFixedpoint θ⌝ := by
      simp [t, substNumeralParams_app_quote, parameterizedFixedpoint]
    calc
      V ⊧/params (parameterizedFixedpoint θ)
        ↔ V ⊧/(t :> params) (parameterizedDiag θ)       := by
          simp [parameterizedFixedpoint, Matrix.comp_vecCons', t, Function.comp_def]
      _ ↔ V ⊧/(substNumeralParams k t t :> params) θ    := by
          simp [parameterizedDiag, Matrix.comp_vecCons', BinderNotation.finSuccItr,
            Function.comp_def]
      _ ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ := by simp [ht]

theorem parameterized_diagonal₁ (θ : ArithmeticSemisentence 2) :
    T ⊢ ∀¹ (parameterizedFixedpoint θ 🡘 θ/[⌜parameterizedFixedpoint θ⌝, #0]) := by
  simpa [allClosure, BinderNotation.finSuccItr, Matrix.fun_eq_vec_one] using
    parameterized_diagonal (T := T) θ

end ParameterizedDiagonalization

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Theory.Δ₁

open Arithmetic Bounding.HierarchySymbol.Semiformula Arithmetic.Bootstrapping
  Arithmetic.Bootstrapping.Arithmetic

variable (φ : ArithmeticSemisentence 1)

noncomputable def numeralInstancesCh : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ n <⁺ x, !ssnum x ↑(⌜φ⌝ : ℕ) n”)
  (.mkPi “x. ∃ n <⁺ x, ∀ y, !ssnum y ↑(⌜φ⌝ : ℕ) n → x = y”)

noncomputable abbrev numeralInstances
    (hφ : ∀ n : ℕ, n ≤ (⌜(φ/[↑n] : ArithmeticSentence)⌝ : ℕ)) :
    Theory.Δ₁ (Set.range fun n : ℕ ↦ (φ/[↑n] : ArithmeticSentence)) where
  ch := numeralInstancesCh φ
  mem_iff ψ := by
    have h (n : ℕ) : substNumeral (⌜φ⌝ : ℕ) n = ⌜(φ/[↑n] : ArithmeticSentence)⌝ := by
      simpa using substNumeral_app_natCast (V := ℕ) φ n;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, numeralInstancesCh, Fin.Fin1.eq_one,
      Fin.isValue, Sentence.coe_quote, val_mkDelta, val_mkSigma, eval_bexsLTSucc',
      Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.eval_substs, Matrix.comp₃,
      Matrix.cons_val_one, Sentence.val_quote, Matrix.cons_val_zero,
      Bounding.HierarchySymbol.Defined.iff, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_app_two, h, Set.mem_range, exists_exists_eq_and];
    constructor;
    · rintro ⟨n, -, hn⟩;
      exact ⟨n, (Semiformula.quote_inj_iff (V := ℕ)).mp hn⟩;
    · rintro ⟨n, rfl⟩;
      exact ⟨n, Nat.eq_or_lt_of_le (hφ n), rfl⟩;
  isDelta1 := ProvablyProperOn.arithmetic_ofProperOn.{0} _ fun V _ _ ↦ by
    intro v;
    simp [numeralInstancesCh];

end FFL.FirstOrder.Theory.Δ₁
