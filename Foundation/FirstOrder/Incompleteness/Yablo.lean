import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint
import Foundation.FirstOrder.Internal.RosserProvability


namespace LO.PeanoMinus

open ORingStruc

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

lemma numeral_lt_of_numeral_succ_lt {n : ℕ} {m : M} : (numeral (n + 1) : M) < m → (numeral n < m) := by
  apply PeanoMinus.lt_trans;
  simp;

end LO.PeanoMinus


namespace LO.ISigma1.Metamath.InternalArithmetic

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

lemma substNumeral_app_quote_nat (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
  substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[.numeral n] : Sentence ℒₒᵣ)⌝ := by
  simp [
    substNumeral, Semiformula.empty_quote_def, Semiformula.quote_def,
    Rewriting.embedding_substs_eq_substs_coe₁
  ];

end LO.ISigma1.Metamath.InternalArithmetic





namespace LO.FirstOrder

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

namespace Theory

variable {V} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]
         {T U : ArithmeticTheory} [T.Δ₁]

def YabloSystem (T : ArithmeticTheory) [T.Δ₁] (φ n : V) : Prop := ∀ m, n < m → ¬T.Provable (substNumeral φ m)

def yabloSystem (T : ArithmeticTheory) [T.Δ₁] : 𝚷₁.Semisentence 2 := .mkPi
  “φ n. ∀ m, n < m → ∀ nσ, !ssnum nσ φ m → ¬!T.provable (nσ)”

lemma yabloSystem.defined : 𝚷₁-Relation[V] (T.YabloSystem) via T.yabloSystem := by
  intro f;
  simp [Theory.YabloSystem, Theory.yabloSystem];

@[simp]
lemma yabloSystem.eval (v) :
   Semiformula.Evalbm V v T.yabloSystem.val ↔ T.YabloSystem (v 0) (v 1) := yabloSystem.defined.df.iff v

instance yabloSystem.definable : 𝚷₁-Relation[V] (T.YabloSystem) := yabloSystem.defined.to_definable


open Classical
open LO.Entailment

/-- Yablo Predicate -/
def yablo (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSemisentence 1 := parameterizedFixedpoint (T.yabloSystem)

abbrev yabloPred (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : ArithmeticSentence := T.yablo/[n]

section

variable {V : Type} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]
variable [𝐈𝚺₁ ⪯ U]

lemma yablo_diagonal : U ⊢!. ∀' (T.yablo ⭤ (T.yabloSystem)/[⌜T.yablo⌝, #0]) := parameterized_diagonal₁ _

lemma yablo_diagonal_modeled (n : V) : V ⊧/![n] (T.yablo) ↔ T.YabloSystem ⌜T.yablo⌝ n := by sorry;
  /-
  have : V ⊧ₘ₀ ∀' (T.yablo ⭤ ↑(T.yabloSystem)/[⌜T.yablo⌝, #0]) := models_of_provable₀ (T := 𝐈𝚺₁) (by assumption) $ yablo_diagonal;
  have : ∀ (n : V), V ⊧/![n] (T.yablo) ↔ T.YabloSystem ⌜T.yablo⌝ n := by simpa [models₀_iff] using this;
  apply this;
  -/


lemma iff_yablo_provable (n : ℕ) : U ⊢!. T.yablo/[n] ↔ U ⊢!. “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” := by
  suffices U ⊢!. T.yablo/[n] ⭤ “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” by
    constructor <;> . intro h; cl_prover [h, this];
  apply oRing_provable₀_of.{0};
  intro V _ _;
  haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ U inferInstance;
  haveI : V ⊧/![ORingStruc.numeral n] (yablo T) ↔ T.YabloSystem ⌜T.yablo⌝ (ORingStruc.numeral n) := yablo_diagonal_modeled _;
  -- simpa [models_iff, Matrix.constant_eq_singleton] using this; TODO: compilation problem
  sorry;

lemma provable_yablo_lt (n m : ℕ) (hnm : n < m) : U ⊢!. (T.yabloPred n) ➝ (T.yabloPred m) := by
  apply oRing_provable₀_of.{0};
  intro V _ _;
  haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ U inferInstance;
  suffices V ⊧/![(ORingStruc.numeral n)] (T.yablo) → V ⊧/![(ORingStruc.numeral m)] (T.yablo) by
    simp only [
      models₀_iff, LogicalConnective.HomClass.map_imply, Semiformula.eval_substs,
      Matrix.cons_val_fin_one, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      LogicalConnective.Prop.arrow_eq
    ];
    convert this <;> simp;
  simp only [yablo_diagonal_modeled];
  intro h k hmk;
  apply h;
  apply PeanoMinus.lt_trans _ _ _ (by simpa) hmk;

end

open LO.Entailment

theorem yablo_unprovable [𝐈𝚺₁ ⪯ T] [Entailment.Consistent T] {n : ℕ} : T ⊬. (T.yabloPred n) := by
  by_contra! hC;
  have H₁ : T ⊢!. T.provabilityPred (T.yablo/[.numeral (n + 1)]) := by
    apply Entailment.WeakerThan.pbl $ provable_D1 (T := T) ?_;
    apply provable_yablo_lt n (n + 1) (by omega) ⨀ hC;
  have H₂ : T ⊢!. ∼T.provabilityPred (T.yablo/[.numeral (n + 1)]) := by
    apply oRing_provable₀_of.{0};
    intro V _ _;
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance;
    suffices ¬T.Provable (substNumeral ⌜yablo T⌝ (n + 1 : V)) by
      simpa [provabilityPred, models_iff, ←substNumeral_app_quote_nat];
    have : ∀ (x : V), ORingStruc.numeral n < x → ¬Provable T (substNumeral ⌜yablo T⌝ x) := by
      sorry;
      /-
      haveI : V ⊧ₘ₀ “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” :=
        models_of_provable₀ (T := T) (by assumption) $ (iff_yablo_provable n |>.mp hC);
      simpa [models_iff] using this; -- TODO: comilation problem
      -/
    apply this (n + 1) (by simp [numeral_eq_natCast]);
  apply Entailment.Consistent.not_bot (𝓢 := T.toAxiom);
  . infer_instance;
  . cl_prover [H₁, H₂];

/-
theorem yablo_unrefutable [T.SoundOnHierarchy 𝚺 1] {n : ℕ} : T ⊬. ∼T.yablo/[n] := by
  have T_consis : Consistent (T : Axiom ℒₒᵣ) := inferInstance;
  by_contra! hC;
  have : T ⊢!. (“∃' (↑n < #0 ∧ !(∀' (↑ssnum/[#0, ⌜yablo T⌝, #1] ➝ ↑(provable T)/[#0])))”) := by
    sorry;
  have := T.soundOnHierarchy 𝚺 1 this (by sorry);
  sorry;
-/

end Theory


end LO.FirstOrder
