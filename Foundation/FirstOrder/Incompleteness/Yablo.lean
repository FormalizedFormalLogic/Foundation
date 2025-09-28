/-
  Formalizing Yablo's Paradox.

  *References*
  - C. Cieśliński, R. Urbaniak, "Gödelizing the Yablo Sequence"
-/

import Foundation.FirstOrder.Internal.DerivabilityCondition

namespace LO.PeanoMinus

open ORingStruc

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝗣𝗔⁻]

lemma numeral_lt_of_numeral_succ_lt {n : ℕ} {m : M} : (numeral (n + 1) : M) < m → (numeral n < m) := by
  apply PeanoMinus.lt_trans;
  simp;

end LO.PeanoMinus


namespace LO.ISigma1.Metamath.InternalArithmetic

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝗜𝚺₁]

lemma substNumeral_app_quote_nat_model (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
  substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[.numeral n] : Sentence ℒₒᵣ)⌝ := by
  simp [
    substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_substs_eq_substs_coe₁
  ];

lemma substNumeral_app_quote_nat_Nat (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
  substNumeral ⌜σ⌝ n = ⌜(σ/[.numeral n] : Sentence ℒₒᵣ)⌝ := by
  simp [
    substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_substs_eq_substs_coe₁
  ];

end LO.ISigma1.Metamath.InternalArithmetic

namespace LO.FirstOrder

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

namespace Theory

variable {V} [ORingStruc V] [V ⊧ₘ* 𝗜𝚺₁]
         {T U : ArithmeticTheory} [T.Δ₁]

def YabloSystem (T : ArithmeticTheory) [T.Δ₁] (φ n : V) : Prop := ∀ m, n < m → ¬T.Provable (substNumeral φ m)

def yabloSystem (T : ArithmeticTheory) [T.Δ₁] : 𝚷₁.Semisentence 2 := .mkPi
  “φ n. ∀ m, n < m → ∀ nσ, !ssnum nσ φ m → ¬!T.provable (nσ)”

lemma yabloSystem.defined : 𝚷₁-Relation[V] (T.YabloSystem) via T.yabloSystem := by
  intro f;
  simp [Theory.YabloSystem, Theory.yabloSystem];

@[simp]
lemma yabloSystem.eval (v) : Semiformula.Evalbm V v T.yabloSystem.val ↔ T.YabloSystem (v 0) (v 1) := yabloSystem.defined.df.iff v

instance yabloSystem.definable : 𝚷₁-Relation[V] (T.YabloSystem) := yabloSystem.defined.to_definable

def yablo (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSemisentence 1 := parameterizedFixedpoint (T.yabloSystem)

abbrev yabloPred (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : ArithmeticSentence := T.yablo/[.numeral n]

end Theory



namespace Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

open Theory

-- Lemmata
section

variable {V : Type} [ORingStruc V] [V ⊧ₘ* 𝗜𝚺₁]
variable {U : ArithmeticTheory} [𝗜𝚺₁ ⪯ U]

lemma yablo_diagonal : U ⊢ ∀' (T.yablo ⭤ (T.yabloSystem)/[⌜T.yablo⌝, #0]) := parameterized_diagonal₁ _

lemma yablo_diagonal_modeled (n : V) : V ⊧/![n] (T.yablo) ↔ ∀ m, n < m → ¬T.Provable (substNumeral ⌜T.yablo⌝ m) := by
  have : V ⊧ₘ ∀' (T.yablo ⭤ ↑(T.yabloSystem)/[⌜T.yablo⌝, #0]) := models_of_provable (T := 𝗜𝚺₁) (by assumption) $ yablo_diagonal;
  have : ∀ (n : V), V ⊧/![n] (T.yablo) ↔ T.YabloSystem ⌜T.yablo⌝ n := by simpa [models_iff, Matrix.comp_vecCons'] using this;
  apply this;

lemma yablo_diagonal_neg_modeled (n : V) : ¬V ⊧/![n] (T.yablo) ↔ ∃ m, n < m ∧ T.Provable (substNumeral ⌜T.yablo⌝ m) := by
  simpa using yablo_diagonal_modeled n |>.not;

lemma iff_yablo_provable (n : ℕ) : U ⊢ T.yabloPred n ↔ U ⊢ “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” := by
  suffices U ⊢ T.yablo/[n] ⭤ “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” by
    constructor <;> . intro h; cl_prover [h, this];
  apply oRing_provable_of.{0};
  intro V _ _;
  haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ U inferInstance;
  haveI : V ⊧/![ORingStruc.numeral n] (T.yablo) ↔ T.YabloSystem ⌜T.yablo⌝ (ORingStruc.numeral n) := yablo_diagonal_modeled _;
  simpa [models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons'] using this;

lemma iff_neg_yablo_provable (n : ℕ) : U ⊢ ∼(T.yabloPred n) ↔ U ⊢ “∃ m, ↑n < m ∧ ∃ nσ, !ssnum nσ ⌜T.yablo⌝ m ∧ !T.provable (nσ)” := by
  suffices U ⊢ ∼T.yablo/[n] ⭤ “∃ m, ↑n < m ∧ ∃ nσ, !ssnum nσ ⌜T.yablo⌝ m ∧ !T.provable (nσ)” by
    constructor <;> . intro h; cl_prover [h, this];
  apply oRing_provable_of.{0};
  intro V _ _;
  haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ U inferInstance;
  haveI : ¬V ⊧/![ORingStruc.numeral n] (T.yablo) ↔ ∃ m, ORingStruc.numeral n < m ∧ Provable T (substNumeral ⌜T.yablo⌝ m) := yablo_diagonal_neg_modeled _;
  simpa [models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons'] using this;

lemma provable_greater_yablo {n m : ℕ} (hnm : n < m) : U ⊢ T.yabloPred n ➝ T.yabloPred m := by
  apply oRing_provable_of.{0};
  intro V _ _;
  haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ U inferInstance;
  suffices
    (∀ m, ORingStruc.numeral n < m → ¬Provable T (substNumeral ⌜yablo T⌝ m)) →
    (∀ k, ORingStruc.numeral m < k → ¬Provable T (substNumeral ⌜yablo T⌝ k))
    by simpa [models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', yablo_diagonal_modeled] using this;
  intro h k hmk;
  apply h;
  apply PeanoMinus.lt_trans _ _ _ (by simpa) hmk;

end

-- Main Results
section

variable [𝗜𝚺₁ ⪯ T] {n : ℕ}

theorem yablo_unprovable [Entailment.Consistent T] : T ⊬ (T.yabloPred n) := by
  by_contra! hC;
  have H₁ : T ⊢ T.provabilityPred (T.yabloPred (n + 1)) := by
    apply Entailment.WeakerThan.pbl $ provable_D1 (T := T) ?_;
    apply provable_greater_yablo (show n < n + 1 by omega) ⨀ hC;
  have H₂ : T ⊢ ∼T.provabilityPred (T.yabloPred (n + 1)) := by
    apply oRing_provable_of.{0};
    intro V _ _;
    haveI : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance;
    suffices ¬T.Provable (substNumeral ⌜T.yablo⌝ (n + 1 : V)) by
      simpa [provabilityPred, models_iff, ←substNumeral_app_quote_nat_model];
    have : ∀ (x : V), ORingStruc.numeral n < x → ¬T.Provable (substNumeral ⌜T.yablo⌝ x) := by
      have : V ⊧ₘ “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” :=
        models_of_provable (T := T) (by assumption) $ (iff_yablo_provable n |>.mp hC);
      simpa [models_iff, Matrix.comp_vecCons'] using this;
    apply this (n + 1) (by simp [numeral_eq_natCast]);
  apply Entailment.Consistent.not_bot (𝓢 := T);
  . infer_instance;
  . cl_prover [H₁, H₂];

theorem yablo_unrefutable [T.SoundOnHierarchy 𝚺 1] : T ⊬ ∼T.yabloPred n := by
  by_contra! hC;
  haveI := T.soundOnHierarchy 𝚺 1 (iff_neg_yablo_provable n |>.mp hC) $ by simp;
  obtain ⟨k, _, hk⟩ : ∃ k, n < k ∧ Provable T (substNumeral ⌜T.yablo⌝ k) := by simpa [models_iff, Matrix.comp_vecCons'] using this;
  rw [substNumeral_app_quote_nat_Nat, provable_iff_provable (T := T)] at hk;
  exact yablo_unprovable hk;

theorem yablo_independent [T.SoundOnHierarchy 𝚺 1] : Entailment.Independent T (T.yabloPred n) := ⟨yablo_unprovable, yablo_unrefutable⟩

end

end Arithmetic


end LO.FirstOrder
