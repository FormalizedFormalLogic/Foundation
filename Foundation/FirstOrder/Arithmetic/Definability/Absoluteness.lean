module

public import Foundation.FirstOrder.Arithmetic.Definability.BoundedDefinable

@[expose] public section
namespace LO.FirstOrder.Arithmetic

open PeanoMinus R0

lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence ℒₒᵣ k} :
    ℕ ⊧/v φ ↔ ℕ ⊧ₘ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff]

variable (V : Type*) [ORingStructure V] [V ⊧ₘ* 𝗣𝗔⁻]

lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence ℒₒᵣ k} :
    V ⊧/(v ·) φ ↔ V ⊧ₘ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (φ : 𝚺₀.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val ↔ V ⊧/(v ·) φ.val :=
  ⟨by simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs] using nat_extention_sigmaOne V (by simp),
   by simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs] using nat_extention_piOne V (by simp)⟩

lemma Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {φ : 𝚺₀.Semisentence k}
    (hR : 𝚺₀.Defined R φ) (hR' : 𝚺₀.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa [hR.iff, hR'.iff] using Arithmetic.shigmaZero_absolute V φ v

lemma DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {φ : 𝚺₀.Semisentence (k + 1)}
    (hf : 𝚺₀.DefinedFunction f φ) (hf' : 𝚺₀.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaZero_absolute V hf hf' (f v :> v)

lemma sigmaOne_upward_absolute {k} (φ : 𝚺₁.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val → V ⊧/(v ·) φ.val := by
  simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  using nat_extention_sigmaOne V (by simp)

lemma piOne_downward_absolute {k} (φ : 𝚷₁.Semisentence k) (v : Fin k → ℕ) :
    V ⊧/(v ·) φ.val → ℕ ⊧/v φ.val := by
  simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  using nat_extention_piOne V (by simp)

lemma deltaOne_absolute {k} (φ : 𝚫₁.Semisentence k)
    (properNat : φ.ProperOn ℕ) (proper : φ.ProperOn V) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val ↔ V ⊧/(v ·) φ.val :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute V φ.sigma v,
   by simpa [proper.iff', properNat.iff'] using piOne_downward_absolute V φ.pi v⟩

lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {φ : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R φ) (hR' : 𝚫₁.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa using deltaOne_absolute V φ hR.proper hR'.proper v

lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {φ : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f φ) (hf' : 𝚺₁.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaOne_absolute V hf.graph_delta hf'.graph_delta (f v :> v)

variable {V}

lemma models_iff_of_Sigma0 {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ := by
  by_cases h : ℕ ⊧/e σ <;> simp [h]
  · have : V ⊧/(e ·) σ := by
      simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) h
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (∼σ) := by simpa using h
    have : V ⊧/(e ·) (∼σ) := by simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) this
    simpa using this

lemma models_iff_of_Delta1 {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val := by
  by_cases h : ℕ ⊧/e σ.val <;> simp [h]
  · have : ℕ ⊧/e σ.sigma.val := by simpa [HierarchySymbol.Semiformula.val_sigma] using h
    have : V ⊧/(e ·) σ.sigma.val := by simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (∼σ.pi.val) := by simpa [hσ.iff'] using h
    have : V ⊧/(e ·) (∼σ.pi.val) := by simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [hσV.iff'] using this

variable {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

noncomputable instance : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance

theorem sigma_one_completeness_iff_param {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := Iff.trans
  (by simp [models_iff, Semiformula.eval_substs])
  (sigma_one_completeness_iff (T := T) (by simp [hσ]))

lemma models_iff_provable_of_Sigma0_param [V ⊧ₘ* T] {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ        := by
      simp [models_iff_of_Sigma0 hσ]
  _             ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])

lemma models_iff_provable_of_Delta1_param [V ⊧ₘ* T] {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val        := by
      simp [models_iff_of_Delta1 hσ hσV]
  _                 ↔ ℕ ⊧/e σ.sigma.val  := by
      simp [HierarchySymbol.Semiformula.val_sigma]
  _                 ↔ T ⊢ (σ.sigma.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp)
  _                 ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))       := by
      simp [HierarchySymbol.Semiformula.val_sigma]

end Arithmetic

end LO.FirstOrder
