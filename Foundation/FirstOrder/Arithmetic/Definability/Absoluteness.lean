module

public import Foundation.FirstOrder.Arithmetic.Definability.BoundedDefinable
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness

@[expose] public section
namespace FFL.FirstOrder.Arithmetic

open PeanoMinus R0

lemma nat_modelsWithParam_iff_models_substs {k : ℕ} {v : Fin k → ℕ} {φ : ArithmeticSemisentence k} :
    φ.Evalb v ↔ ℕ↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, Function.comp_def, Matrix.empty_eq]

variable (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The natural-number embedding into a model of Peano arithmetic without induction.
This is the routine structure-embedding form of the natural cast. -/
def natCastEmbedding : ℕ ↪ₛ[ℒₒᵣ] V where
  toFun := Nat.cast
  func' := by
    intro k f v
    cases f with
    | zero => exact Nat.cast_zero
    | one => exact Nat.cast_one
    | add => exact Nat.cast_add _ _
    | mul => exact Nat.cast_mul _ _
  rel' := by
    intro k r v
    cases r with
    | eq => exact Nat.cast_inj.mpr
    | lt => exact Nat.cast_lt.mpr
  toFun_inj := Nat.cast_injective
  rel_inv' := by
    intro k r v
    cases r with
    | eq => exact Nat.cast_inj.mp
    | lt => exact Nat.cast_lt.mp

@[simp] lemma natCastEmbedding_apply (n : ℕ) : natCastEmbedding V n = (n : V) := rfl

instance : (ℬ[<, ℒₒᵣ]).IsInitial (natCastEmbedding V) where
  operator_iff := by
    intro R hR a b
    obtain rfl := Set.mem_singleton_iff.mp hR
    simp
  initial := by
    intro R hR a b hb
    obtain rfl := Set.mem_singleton_iff.mp hR
    have hb : b < (a : V) := by simpa using hb
    obtain ⟨c, rfl⟩ := eq_nat_of_lt_nat hb
    exact ⟨c, rfl⟩

lemma modelsWithParam_iff_models_substs {k : ℕ} {v : Fin k → ℕ}
    {φ : ArithmeticSemisentence k} :
    φ.Evalb (M := V) (Nat.cast ∘ v) ↔ V↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦
      Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, Function.comp_def, Matrix.empty_eq, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (φ : 𝚺₀.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v) :=
  Bounding.shigmaZero_absolute (natCastEmbedding V) φ v

lemma Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop}
    {φ : 𝚺₀.Semisentence k}
    (hR : 𝚺₀.Defined R φ) (hR' : 𝚺₀.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (Nat.cast ∘ v) :=
  Bounding.HierarchySymbol.Defined.shigmaZero_absolute (natCastEmbedding V) hR hR' v

lemma DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V}
    {φ : 𝚺₀.Semisentence (k + 1)}
    (hf : 𝚺₀.DefinedFunction f φ) (hf' : 𝚺₀.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (Nat.cast ∘ v) :=
  Bounding.HierarchySymbol.DefinedFunction.shigmaZero_absolute_func (natCastEmbedding V) hf hf' v

lemma sigmaOne_upward_absolute {k} (φ : 𝚺₁.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb v → φ.val.Evalb (M := V) (Nat.cast ∘ v) :=
  Bounding.sigmaOne_upward_absolute (natCastEmbedding V) φ v

lemma piOne_downward_absolute {k} (φ : 𝚷₁.Semisentence k) (v : Fin k → ℕ) :
    φ.val.Evalb (M := V) (Nat.cast ∘ v) → φ.val.Evalb v :=
  Bounding.piOne_downward_absolute (natCastEmbedding V) φ v

lemma deltaOne_absolute {k} (φ : 𝚫₁.Semisentence k)
    (properNat : φ.ProperOn ℕ) (proper : φ.ProperOn V) (v : Fin k → ℕ) :
    φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v) :=
  Bounding.deltaOne_absolute (natCastEmbedding V) φ properNat proper v

lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop}
    {φ : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R φ) (hR' : 𝚫₁.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (Nat.cast ∘ v) :=
  Bounding.HierarchySymbol.Defined.shigmaOne_absolute (natCastEmbedding V) hR hR' v

lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V}
    {φ : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f φ) (hf' : 𝚺₁.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (Nat.cast ∘ v) :=
  Bounding.HierarchySymbol.DefinedFunction.shigmaOne_absolute_func (natCastEmbedding V) hf hf' v

variable {V}

lemma models_iff_of_Sigma0 {n : ℕ} {σ : ArithmeticSemisentence n}
    (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    σ.Evalb (M := V) (Nat.cast ∘ e) ↔ σ.Evalb e :=
  Bounding.models_iff_of_Sigma0 (natCastEmbedding V) hσ

lemma models_iff_of_Delta1 {n : ℕ} {σ : 𝚫₁.Semisentence n}
    (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    σ.val.Evalb (M := V) (Nat.cast ∘ e) ↔ σ.val.Evalb e :=
  Bounding.models_iff_of_Delta1 (natCastEmbedding V) hσ hσV

variable {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

noncomputable instance : 𝗥₀ ⪯ T :=
  Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance

theorem sigma_one_completeness_iff_param {n : ℕ} {σ : ArithmeticSemisentence n}
    (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := Iff.trans
  (by simp [models_iff, Semiformula.eval_substs, Function.comp_def, Matrix.empty_eq])
  (sigma_one_completeness_iff (T := T) (by simp [hσ]))

lemma models_iff_provable_of_Sigma0_param [V↓[ℒₒᵣ] ⊧* T] {n : ℕ} {σ : ArithmeticSemisentence n}
    (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(Nat.cast ∘ e) σ ↔ ℕ ⊧/e σ        := by
      simp [models_iff_of_Sigma0 hσ]
  _             ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])

lemma models_iff_provable_of_Delta1_param [V↓[ℒₒᵣ] ⊧* T] {n : ℕ} {σ : 𝚫₁.Semisentence n}
    (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ.val ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(Nat.cast ∘ e) σ.val ↔ ℕ ⊧/e σ.val        := by
      simp [models_iff_of_Delta1 hσ hσV]
  _                 ↔ ℕ ⊧/e σ.sigma.val  := by
      simp [Bounding.HierarchySymbol.Semiformula.val_sigma]
  _                 ↔ T ⊢ (σ.sigma.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp)
  _                 ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))       := by
      simp [Bounding.HierarchySymbol.Semiformula.val_sigma]

end Arithmetic

end FFL.FirstOrder
