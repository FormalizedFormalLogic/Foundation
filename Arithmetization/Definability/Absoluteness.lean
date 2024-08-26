import Arithmetization.Definability.BoundedBoldface

namespace LO.FirstOrder.Arith

open LO.Arith

lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {p : Semisentence ℒₒᵣ k} :
    ℕ ⊧/v p ↔ ℕ ⊧ₘ (Rew.substs (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)) |>.hom p) := by
  simp [models_iff]

variable (V : Type*) [ORingStruc V] [V ⊧ₘ* 𝐏𝐀⁻]

lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {p : Semisentence ℒₒᵣ k} :
    V ⊧/(v ·) p ↔ V ⊧ₘ (Rew.substs (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)) |>.hom p) := by
  simp [models_iff, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (p : 𝚺₀.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v p.val ↔ V ⊧/(v ·) p.val :=
  ⟨by simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]; exact nat_extention_sigmaOne V (by simp),
   by simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]; exact nat_extention_piOne V (by simp)⟩

lemma Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {p : 𝚺₀.Semisentence k}
    (hR : 𝚺₀.Defined R p) (hR' : 𝚺₀.Defined R' p) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa [hR.iff, hR'.iff] using Arith.shigmaZero_absolute V p v

lemma DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {p : 𝚺₀.Semisentence (k + 1)}
    (hf : 𝚺₀.DefinedFunction f p) (hf' : 𝚺₀.DefinedFunction f' p) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaZero_absolute V hf hf' (f v :> v)

lemma sigmaOne_upward_absolute {k} (p : 𝚺₁.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v p.val → V ⊧/(v ·) p.val := by
  simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_sigmaOne V (by simp)

lemma piOne_downward_absolute {k} (p : 𝚷₁.Semisentence k) (v : Fin k → ℕ) :
    V ⊧/(v ·) p.val → ℕ ⊧/v p.val := by
  simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_piOne V (by simp)

lemma deltaOne_absolute {k} (p : 𝚫₁.Semisentence k)
    (properNat : p.ProperOn ℕ) (proper : p.ProperOn V) (v : Fin k → ℕ) :
    ℕ ⊧/v p.val ↔ V ⊧/(v ·) p.val :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute V p.sigma v,
   by simpa [proper.iff', properNat.iff'] using piOne_downward_absolute V p.pi v⟩

lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {p : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R p) (hR' : 𝚫₁.Defined R' p) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa [hR.df.iff, hR'.df.iff] using deltaOne_absolute V p hR.proper hR'.proper v

lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {p : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f p) (hf' : 𝚺₁.DefinedFunction f' p) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaOne_absolute V hf.graph_delta hf'.graph_delta (f v :> v)

variable {V}

lemma models_iff_of_Sigma0 {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ := by
  by_cases h : ℕ ⊧/e σ <;> simp [h]
  · have : V ⊧/(e ·) σ := by
      simpa [Matrix.empty_eq] using LO.Arith.bold_sigma_one_completeness (M := V) (by simp [Hierarchy.of_zero hσ]) h
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (~σ) := by simpa using h
    have : V ⊧/(e ·) (~σ) := by simpa [Matrix.empty_eq] using LO.Arith.bold_sigma_one_completeness (M := V) (by simp [Hierarchy.of_zero hσ]) this
    simpa using this

lemma models_iff_of_Delta1 {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val := by
  by_cases h : ℕ ⊧/e σ.val <;> simp [h]
  · have : ℕ ⊧/e σ.sigma.val := by simpa [HierarchySymbol.Semiformula.val_sigma] using h
    have : V ⊧/(e ·) σ.sigma.val := by simpa [Matrix.empty_eq] using LO.Arith.bold_sigma_one_completeness (M := V) (by simp) this
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (~σ.pi.val) := by simpa [hσ.iff'] using h
    have : V ⊧/(e ·) (~σ.pi.val) := by simpa [Matrix.empty_eq] using LO.Arith.bold_sigma_one_completeness (M := V) (by simp) this
    simpa [hσV.iff'] using this

variable {T : Theory ℒₒᵣ} [𝐏𝐀⁻ ≼ T] [ℕ ⊧ₘ* T]

theorem sigma_one_completeness_iff_param {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ := Iff.trans
  (by simp [models_iff, Semiformula.eval_substs])
  (sigma_one_completeness_iff (by simp [hσ]))

lemma models_iff_provable_of_Sigma0_param [V ⊧ₘ* T] {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ := by
  calc
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ        := by
      simp [models_iff_of_Sigma0 hσ]
  _             ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ := by
      apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])

lemma models_iff_provable_of_Delta1_param [V ⊧ₘ* T] {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ := by
  calc
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val        := by
      simp [models_iff_of_Delta1 hσ hσV]
  _                 ↔ ℕ ⊧/e σ.sigma.val  := by
      simp [HierarchySymbol.Semiformula.val_sigma]
  _                 ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ.sigma.val := by
      apply sigma_one_completeness_iff_param (by simp)
  _                 ↔ T ⊢₌! (Rew.substs fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)).hom σ.val       := by
      simp [HierarchySymbol.Semiformula.val_sigma]

end Arith

end LO.FirstOrder
