module

public import Foundation.FirstOrder.Bootstrapping.Syntax

@[expose] public section
open Classical

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

namespace Bootstrapping.Arithmetic

noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ

lemma substNumeral_app_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[⌜π⌝] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁]

noncomputable def substNumerals (φ : V) (v : Fin k → V) : V := subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ

lemma substNumerals_app_quote (σ : Semisentence ℒₒᵣ k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝ := by
  simp [substNumerals, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb]
  rfl

lemma substNumerals_app_quote_quote (σ : Semisentence ℒₒᵣ k) (π : Fin k → Semisentence ℒₒᵣ k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) = ⌜((Rew.subst (fun i ↦ ⌜π i⌝)) ▹ σ : ArithmeticSentence)⌝ := by
  simpa [Sentence.coe_quote_eq_quote] using substNumerals_app_quote (V := V) σ (fun i ↦ ⌜π i⌝)

noncomputable def substNumeralParams (k : ℕ) (φ x : V) : V := subst ℒₒᵣ (matrixToVec (numeral x :> fun i : Fin k ↦ qqBvar i)) φ

lemma substNumeralParams_app_quote (σ τ : Semisentence ℒₒᵣ (k + 1)) :
    (substNumeralParams k ⌜σ⌝ ⌜τ⌝ : V) = ⌜((Rew.subst (⌜τ⌝ :> fun i : Fin k ↦ #i)) ▹ σ : Semisentence ℒₒᵣ k)⌝ := by
  simp [substNumeralParams, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb, Matrix.vecHead]
  rfl

section

noncomputable def ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ n, !numeralGraph n x ∧ ∃ v, !adjoinDef v n 0 ∧ !(substsGraph ℒₒᵣ) y v φ”

instance substNumeral.defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum := .mk fun v ↦ by simp [ssnum, substNumeral]

attribute [irreducible] ssnum

noncomputable def ssnums : 𝚺₁.Semisentence (k + 2) := .mkSigma
  “y φ. ∃ n, !lenDef ↑k n ∧
    (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k).val ∧ !numeralGraph z #i.succ.succ.succ.succ) ∧
    !(substsGraph ℒₒᵣ) y n φ”

instance substNumerals.defined :
    Arithmetic.HierarchySymbol.DefinedFunction (fun v ↦ substNumerals (v 0) (v ·.succ) : (Fin (k + 1) → V) → V) ssnums := .mk fun v ↦ by
  unfold ssnums
  symm
  suffices
      v 0 = subst ℒₒᵣ (matrixToVec fun i ↦ numeral (v i.succ.succ)) (v 1) ↔
      ∃ x, ↑k = len x ∧ (∀ i : Fin k, x.[↑↑i] = numeral (v i.succ.succ)) ∧ v 0 = subst ℒₒᵣ x (v 1) by
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

noncomputable def ssnumParams (k : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ v, !lenDef ↑(k + 1) v ∧
    (∃ z, !nthDef z v 0 ∧ !numeralGraph z x) ∧
    (⋀ i, ∃ z, !nthDef z v ↑(i : Fin k).val.succ ∧ !qqBvarDef z ↑i) ∧
    !(substsGraph ℒₒᵣ) y v φ”

instance ssnumParams.defined :
    𝚺₁-Function₂[V] substNumeralParams k via ssnumParams k := .mk fun v ↦ by
  symm
  unfold ssnumParams
  suffices
      v 0 = subst ℒₒᵣ (numeral (v 2) ∷ matrixToVec fun i ↦ ^#↑i) (v 1) ↔
      ∃ x, ↑(k + 1) = len x ∧ x.[0] = numeral (v 2) ∧ (∀ (i : Fin k), x.[↑i + 1] = ^#↑i) ∧ v 0 = subst ℒₒᵣ x (v 1) by
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

end Bootstrapping.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

variable {T : Theory ℒₒᵣ} [𝗜𝚺₁ ⪯ T]

section Diagonalization

noncomputable def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 := “x. ∀ y, !ssnum y x x → !θ y”

noncomputable def fixedpoint (θ : Semisentence ℒₒᵣ 1) : ArithmeticSentence := (diag θ)/[⌜diag θ⌝]

theorem diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢ fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝] :=
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices V ⊧/![] (fixedpoint θ) ↔ V ⊧/![⌜fixedpoint θ⌝] θ by
      simpa [models_iff, Matrix.constant_eq_singleton]
    let t : V := ⌜diag θ⌝
    have ht : substNumeral t t = ⌜fixedpoint θ⌝ := by
      simp [t, fixedpoint, substNumeral_app_quote]
    calc
      V ⊧/![] (fixedpoint θ)
    _ ↔ V ⊧/![t] (diag θ)         := by simp [fixedpoint, Matrix.constant_eq_singleton, t]
    _ ↔ V ⊧/![substNumeral t t] θ := by simp [diag, Matrix.constant_eq_singleton]
    _ ↔ V ⊧/![⌜fixedpoint θ⌝] θ   := by simp [ht]

end Diagonalization

section Multidiagonalization

/-- $\mathrm{diag}_i(\vec{x}) := (\forall \vec{y})\left[ \left(\bigwedge_j \mathrm{ssnums}(y_j, x_j, \vec{x})\right) \to \theta_i(\vec{y}) \right]$ -/
noncomputable def multidiag (θ : Semisentence ℒₒᵣ k) : Semisentence ℒₒᵣ k :=
  ∀⁰^[k] (
    (Matrix.conj fun j : Fin k ↦ (Rew.subst <| #(j.addCast k) :> #(j.addNat k) :> fun l ↦ #(l.addNat k)) ▹ ssnums.val) ➝
    (Rew.subst fun j ↦ #(j.addCast k)) ▹ θ)

noncomputable def multifixedpoint (θ : Fin k → Semisentence ℒₒᵣ k) (i : Fin k) : ArithmeticSentence := (Rew.subst fun j ↦ ⌜multidiag (θ j)⌝) ▹ (multidiag (θ i))

theorem multidiagonal (θ : Fin k → Semisentence ℒₒᵣ k) :
    T ⊢ multifixedpoint θ i ⭤ (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i) :=
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices V ⊧/![] (multifixedpoint θ i) ↔ V ⊧/(fun i ↦ ⌜multifixedpoint θ i⌝) (θ i) by simpa [models_iff]
    let t : Fin k → V := fun i ↦ ⌜multidiag (θ i)⌝
    have ht : ∀ i, substNumerals (t i) t = ⌜multifixedpoint θ i⌝ := by
      intro i; simp [t, multifixedpoint, substNumerals_app_quote_quote]
    calc
      V ⊧/![] (multifixedpoint θ i)
        ↔ V ⊧/t (multidiag (θ i))                   := by simp [t, multifixedpoint]
      _ ↔ V ⊧/(fun i ↦ substNumerals (t i) t) (θ i) := by simp [multidiag, ← funext_iff]
      _ ↔ V ⊧/(fun i ↦ ⌜multifixedpoint θ i⌝) (θ i) := by simp [ht]

noncomputable def exclusiveMultifixedpoint (θ : Fin k → Semisentence ℒₒᵣ k) (i : Fin k) : ArithmeticSentence :=
  multifixedpoint (fun j ↦ (θ j).padding j) i

@[simp] lemma exclusiveMultifixedpoint_inj_iff (θ : Fin k → Semisentence ℒₒᵣ k) :
    exclusiveMultifixedpoint θ i = exclusiveMultifixedpoint θ j ↔ i = j := by
  constructor
  · unfold exclusiveMultifixedpoint multifixedpoint
    suffices ∀ ω : Rew ℒₒᵣ Empty k Empty 0, ω ▹ multidiag ((θ i).padding i) = ω ▹ multidiag ((θ j).padding j) → i = j by exact this _
    intro
    simp [multidiag, Fin.val_inj]
  · rintro rfl; rfl

theorem exclusiveMultidiagonal (θ : Fin k → Semisentence ℒₒᵣ k) :
    T ⊢ exclusiveMultifixedpoint θ i ⭤ (Rew.subst fun j ↦ ⌜exclusiveMultifixedpoint θ j⌝) ▹ θ i := by
  have : T ⊢ exclusiveMultifixedpoint θ i ⭤ ((Rew.subst fun j ↦ ⌜exclusiveMultifixedpoint θ j⌝) ▹ θ i).padding ↑i := by
    simpa using multidiagonal (T := T) (fun j ↦ (θ j).padding j) (i := i)
  exact Entailment.E!_trans this (Entailment.padding_iff _ _)

lemma multifixedpoint_pi {θ : Fin k → Semisentence ℒₒᵣ k} (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (multifixedpoint θ i) := by
  simpa [multifixedpoint, multidiag, h] using fun _ ↦ Hierarchy.mono (s := 1) (by simp) (by simp)

lemma exclusiveMultifixedpoint_pi {θ : Fin k → Semisentence ℒₒᵣ k} (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (exclusiveMultifixedpoint θ i) := by
  apply multifixedpoint_pi; simp [h]

end Multidiagonalization

section ParameterizedDiagonalization

noncomputable def parameterizedDiag (θ : Semisentence ℒₒᵣ (k + 1)) : Semisentence ℒₒᵣ (k + 1) := “x. ∀ y, !(ssnumParams k) y x x → !θ y ⋯”

noncomputable def parameterizedFixedpoint (θ : Semisentence ℒₒᵣ (k + 1)) : Semisentence ℒₒᵣ k :=
    (Rew.subst (⌜parameterizedDiag θ⌝ :> fun j ↦ #j)) ▹ parameterizedDiag θ

theorem parameterized_diagonal (θ : Semisentence ℒₒᵣ (k + 1)) :
    T ⊢ ∀⁰* (parameterizedFixedpoint θ ⭤ “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”) :=
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices
        ∀ params : Fin k → V,
          V ⊧/params (parameterizedFixedpoint θ) ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ by
      simpa [models_iff, Matrix.comp_vecCons', BinderNotation.finSuccItr]
    intro params
    let t : V := ⌜parameterizedDiag θ⌝
    have ht : substNumeralParams k t t = ⌜parameterizedFixedpoint θ⌝ := by
      simp [t, substNumeralParams_app_quote, parameterizedFixedpoint]
    calc
      V ⊧/params (parameterizedFixedpoint θ)
        ↔ V ⊧/(t :> params) (parameterizedDiag θ)       := by simp [parameterizedFixedpoint, Matrix.comp_vecCons', t]
      _ ↔ V ⊧/(substNumeralParams k t t :> params) θ    := by simp [parameterizedDiag, Matrix.comp_vecCons', BinderNotation.finSuccItr]
      _ ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ := by simp [ht]

theorem parameterized_diagonal₁ (θ : Semisentence ℒₒᵣ 2) :
    T ⊢ ∀⁰ (parameterizedFixedpoint θ ⭤ θ/[⌜parameterizedFixedpoint θ⌝, #0]) := by
  simpa [allClosure, BinderNotation.finSuccItr, Matrix.fun_eq_vec_one] using
    parameterized_diagonal (T := T) θ

end ParameterizedDiagonalization

end LO.FirstOrder.Arithmetic
