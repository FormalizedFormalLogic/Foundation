module

public import Foundation.FirstOrder.Arithmetic.Definability.BoundedDefinable

@[expose] public section
namespace LO.FirstOrder.Arithmetic

open PeanoMinus R0

lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : ArithmeticSemisentence k} :
    φ.Evalb v ↔ ℕ↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, Function.comp_def, Matrix.empty_eq]

variable (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : ArithmeticSemisentence k} :
    φ.Evalb (M := V) (Nat.cast ∘ v) ↔ V↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, Function.comp_def, Matrix.empty_eq, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (φ : 𝚺₀.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v) :=
  ⟨by simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs] using nat_extention_sigmaOne V (by simp),
   by simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs] using nat_extention_piOne V (by simp)⟩

lemma Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {φ : 𝚺₀.Semisentence k}
    (hR : 𝚺₀.Defined R φ) (hR' : 𝚺₀.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (Nat.cast ∘ v) := by
  simpa [hR.iff, hR'.iff] using Arithmetic.shigmaZero_absolute V φ v

lemma DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {φ : 𝚺₀.Semisentence (k + 1)}
    (hf : 𝚺₀.DefinedFunction f φ) (hf' : 𝚺₀.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (Nat.cast ∘ v) := by
  simpa [Function.comp_def] using Defined.shigmaZero_absolute V hf hf' (f v :> v)

lemma sigmaOne_upward_absolute {k} (φ : 𝚺₁.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb v → φ.val.Evalb (M := V) (Nat.cast ∘ v) := by
  simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  using nat_extention_sigmaOne V (by simp)

lemma piOne_downward_absolute {k} (φ : 𝚷₁.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb (M := V) (Nat.cast ∘ v) → φ.val.Evalb v := by
  simpa [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  using nat_extention_piOne V (by simp)

lemma deltaOne_absolute {k} (φ : 𝚫₁.Semisentence k)
    (properNat : φ.ProperOn ℕ) (proper : φ.ProperOn V) (v : Fin k → ℕ) :
    φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v) :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute V φ.sigma v,
   by simpa [proper.iff', properNat.iff'] using piOne_downward_absolute V φ.pi v⟩

lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {φ : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R φ) (hR' : 𝚫₁.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (Nat.cast ∘ v) := by
  simpa using deltaOne_absolute V φ hR.proper hR'.proper v

lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {φ : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f φ) (hf' : 𝚺₁.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (Nat.cast ∘ v) := by
  simpa [Function.comp_def] using Defined.shigmaOne_absolute V hf.graph_delta hf'.graph_delta (f v :> v)

variable {V}

lemma models_iff_of_Sigma0 {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    σ.Evalb (M := V) (Nat.cast ∘ e) ↔ σ.Evalb e := by
  by_cases h : σ.Evalb e <;> simp [h]
  · have : σ.Evalb (M := V) (Nat.cast ∘ e) := by
      simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) h
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : (∼σ).Evalb (M := ℕ) e := by simpa using h
    have : (∼σ).Evalb (M := V) (Nat.cast ∘ e) := by
      simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) this
    simpa using this

lemma models_iff_of_Delta1 {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    σ.val.Evalb (M := V) (Nat.cast ∘ e) ↔ σ.val.Evalb e := by
  by_cases h : σ.val.Evalb e <;> simp [h]
  · have : σ.sigma.val.Evalb e := by simpa [HierarchySymbol.Semiformula.val_sigma] using h
    have : σ.sigma.val.Evalb (M := V) (Nat.cast ∘ e) := by simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : (∼σ.pi.val).Evalb (M := ℕ) e := by simpa [hσ.iff'] using h
    have : (∼σ.pi.val).Evalb (M := V) (Nat.cast ∘ e) := by
      simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [hσV.iff'] using this

variable {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

noncomputable instance : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance

theorem sigma_one_completeness_iff_param {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := Iff.trans
  (by simp [models_iff, Semiformula.eval_substs, Function.comp_def, Matrix.empty_eq])
  (sigma_one_completeness_iff (T := T) (by simp [hσ]))

lemma models_iff_provable_of_Sigma0_param [V↓[ℒₒᵣ] ⊧* T] {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(Nat.cast ∘ e) σ ↔ ℕ ⊧/e σ        := by
      simp [models_iff_of_Sigma0 hσ]
  _             ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])

lemma models_iff_provable_of_Delta1_param [V↓[ℒₒᵣ] ⊧* T] {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ.val ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(Nat.cast ∘ e) σ.val ↔ ℕ ⊧/e σ.val        := by
      simp [models_iff_of_Delta1 hσ hσV]
  _                 ↔ ℕ ⊧/e σ.sigma.val  := by
      simp [HierarchySymbol.Semiformula.val_sigma]
  _                 ↔ T ⊢ (σ.sigma.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp)
  _                 ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))       := by
      simp [HierarchySymbol.Semiformula.val_sigma]

end Arithmetic

end LO.FirstOrder
