import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Internal.DerivabilityCondition
import Mathlib.Data.Nat.PartENat

namespace LO.FirstOrder.ArithmeticTheory

variable {T : ArithmeticTheory} [T.Δ₁]

section

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def iIncon (T : ArithmeticTheory) [T.Δ₁] : ℕ → 𝚺₁.Sentence
  |     0 => ⊥
  | n + 1 => T.provabilityPred' (T.iIncon n)

variable (T V)

def IIncon : ℕ → Prop
  |     0 => False
  | n + 1 => T.Provable (⌜(T.iIncon n).val⌝ : V)

variable {T V}

@[simp] lemma IIncon.zero : ¬T.IIncon V 0 := by simp [IIncon]

lemma IIncon.succ_iff :
    T.IIncon V (n + 1) ↔ T.Provable (⌜(T.iIncon n).val⌝ : V) := by simp [IIncon]

@[simp] lemma iIncon_val :
    V ⊧/v (T.iIncon n).val ↔ T.IIncon V n := by
  cases n <;> simp [iIncon, IIncon.succ_iff]

namespace IIncon

variable [𝐏𝐀⁻ ⪯ T]

lemma succ {n} : T.IIncon V n → T.IIncon V (n + 1) := by
  match n with
  |     0 => simp
  | n + 1 => simpa [iIncon] using provable_internalize T

lemma monotone {n m} : n ≤ m → T.IIncon V n → T.IIncon V m := by
  intro _ hn
  revert m
  suffices ∀ k, T.IIncon V (n + k) by
    intro m hnm
    simpa [Nat.add_sub_of_le hnm] using this (m - n)
  intro k
  induction k
  case zero => simpa
  case succ k ih =>
    simpa [add_assoc] using ih.succ

end IIncon

end

open Classical

variable (T)

noncomputable def height : PartENat := PartENat.find (T ⊢!. T.iIncon ·)

variable {T}

lemma height_eq_top_iff : T.height = ⊤ ↔ ∀ n, T ⊬. T.iIncon n := PartENat.find_eq_top_iff _

lemma height_eq_nat_iff {n : ℕ} : T.height = n ↔ T ⊢!. T.iIncon n ∧ ∀ m < n, T ⊬. T.iIncon m := by
  sorry

variable (T)

lemma iIncon_unprovable_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : ∀ n, T ⊬. T.iIncon n
  |     0 => Entailment.consistent_iff_unprovable_bot.mp inferInstance
  | n + 1 => fun h ↦
    have : T ⊢!. ↑(T.iIncon n) := by
      simpa [iIncon, models₀_iff] using T.soundOnHierarchy 𝚺 1 h (by simp)
    iIncon_unprovable_of_sigma1_sound n this

lemma hight_eq_top_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : T.height = ⊤ :=
  height_eq_top_iff.mpr (iIncon_unprovable_of_sigma1_sound T)

lemma hight_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : T.height = 0 := by sorry

variable {T}

@[simp] lemma ISigma1_hight_eq_top : 𝐈𝚺₁.height = ⊤ := hight_eq_top_of_sigma1_sound 𝐈𝚺₁

@[simp] lemma Peano_hight_eq_top : 𝐏𝐀.height = ⊤ := hight_eq_top_of_sigma1_sound 𝐏𝐀

end LO.FirstOrder.ArithmeticTheory
