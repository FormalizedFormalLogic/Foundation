import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Internal.DerivabilityCondition
import Mathlib.Data.Nat.PartENat

namespace LO.FirstOrder.ArithmeticTheory

variable {T : ArithmeticTheory} [T.Δ₁]

section

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def iteratedInconsistency (T : ArithmeticTheory) [T.Δ₁] : ℕ → 𝚺₁.Sentence
  |     0 => ⊥
  | n + 1 => T.provabilityPred' (T.iteratedInconsistency n)

variable (V)

def IteratedInconsistency : ℕ → Prop
  |     0 => False
  | n + 1 => T.Provable (⌜(T.iteratedInconsistency n).val⌝ : V)

variable {V}

@[simp] lemma IteratedInconsistency.zero : ¬T.IteratedInconsistency V 0 := by simp [IteratedInconsistency]

@[simp] lemma IteratedInconsistency.succ :
    T.IteratedInconsistency V (n + 1) ↔ T.Provable (⌜(T.iteratedInconsistency n).val⌝ : V) := by simp [IteratedInconsistency]

end

open Classical

variable (T)

noncomputable def height : PartENat := PartENat.find (T ⊢!. T.iteratedInconsistency ·)

variable {T}

lemma height_eq_top_iff : T.height = ⊤ ↔ ∀ n, T ⊬. T.iteratedInconsistency n := PartENat.find_eq_top_iff _

lemma height_eq_nat_iff {n : ℕ} : T.height = n ↔ T ⊢!. T.iteratedInconsistency n ∧ ∀ m < n, T ⊬. T.iteratedInconsistency m := by
  sorry

variable (T)

lemma iteratedInconsistency_unprovable_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : ∀ n, T ⊬. T.iteratedInconsistency n
  |     0 => Entailment.consistent_iff_unprovable_bot.mp inferInstance
  | n + 1 => fun h ↦
    have : T ⊢!. ↑(T.iteratedInconsistency n) := by
      simpa [iteratedInconsistency, models₀_iff] using T.soundOnHierarchy 𝚺 1 h (by simp)
    iteratedInconsistency_unprovable_of_sigma1_sound n this

lemma hight_eq_top_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : T.height = ⊤ :=
  height_eq_top_iff.mpr (iteratedInconsistency_unprovable_of_sigma1_sound T)

lemma hight_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : T.height = 0 := by sorry

variable {T}

@[simp] lemma ISigma1_hight_eq_top : 𝐈𝚺₁.height = ⊤ := hight_eq_top_of_sigma1_sound 𝐈𝚺₁

@[simp] lemma Peano_hight_eq_top : 𝐏𝐀.height = ⊤ := hight_eq_top_of_sigma1_sound 𝐏𝐀

end LO.FirstOrder.ArithmeticTheory
