import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint
import Foundation.FirstOrder.Internal.RosserProvability

namespace LO.FirstOrder

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

namespace Theory

variable {V} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]
         {T U : ArithmeticTheory} [T.Δ₁] [𝐈𝚺₁ ⪯ U]

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


/-- Yablo's Predicate -/
def yablo (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSemisentence 1 := parameterizedFixedpoint (T.yabloSystem)

lemma yablo_diagonal : U ⊢!. ∀' (T.yablo ⭤ (T.yabloSystem)/[⌜T.yablo⌝, #0]) := parameterized_diagonal₁ _

lemma yablo_def {n : ℕ} : U ⊢!. T.yablo/[n] ↔ U ⊢!. “∀ m, ↑n < m → ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → ¬!T.provable (nσ)” := by
  sorry;

lemma neg_yablo_def {n : ℕ} : U ⊢!. ∼T.yablo/[n] ↔ U ⊢!. “∃ m, ↑n < m ∧ ∀ nσ, !ssnum nσ ⌜T.yablo⌝ m → !T.provable (nσ)” := by
  sorry;

open LO.Entailment
variable [U.Δ₁] [Entailment.Consistent U]

theorem yablo_unprovable [Entailment.Consistent U] {n : ℕ} : U ⊬. T.yablo/[n] := by
  by_contra! hC;
  have := yablo_def.mp hC;
  -- have h₁ : U ⊢!. ∼↑(T.provable)/[⌜(T.yablo)/[n + 1]⌝])))”) := by sorry;
  -- have h₂ : U ⊢!. ↑(T.provable)/[⌜(T.yablo)/[n + 1]⌝])))”) := by sorry;
  have : ¬Entailment.Consistent U := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr $ by
    sorry
  contradiction;

theorem yablo_unrefutable [U.SoundOnHierarchy 𝚺 1] {n : ℕ} : U ⊬. ∼T.yablo/[n] := by
  have con : Consistent (U : Axiom ℒₒᵣ) := inferInstance;
  by_contra! hC;
  have : U ⊢!. (“∃' (↑n < #0 ∧ !(∀' (↑ssnum/[#0, ⌜yablo T⌝, #1] ➝ ↑(provable T)/[#0])))”) := by
    sorry;
  have := U.soundOnHierarchy 𝚺 1 this (by sorry);
  sorry;

end Theory

end LO.FirstOrder
