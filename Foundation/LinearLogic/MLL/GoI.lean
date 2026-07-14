module

public import Foundation.LinearLogic.MLL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Simplified Geometry of Interaction
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.Multiplicative

namespace GoI

@[ext]
structure Project (Carrier : Type*) : Type _ where
  /-- Wager, a remnant of internal cycles. -/
  wager : ℕ
  /-- A main gadget expresses permutation of loci. -/
  plot : Equiv.Perm Carrier

namespace Project

variable {α β : Type*}

def add (𝔞 : Project α) (𝔟 : Project β) : Project (α ⊕ β) where
  wager := 𝔞.wager + 𝔟.wager
  plot := 𝔞.plot.sumCongr 𝔟.plot

instance : HAdd (Project α) (Project β) (Project (α ⊕ β)) where
  hAdd := add

@[simp] lemma add_wager (𝔞 : Project α) (𝔟 : Project β) :
    (𝔞 + 𝔟).wager = 𝔞.wager + 𝔟.wager := rfl

@[simp] lemma add_plot (𝔞 : Project α) (𝔟 : Project β) :
    (𝔞 + 𝔟).plot = 𝔞.plot.sumCongr 𝔟.plot := rfl

def one : Project α where
  wager := 0
  plot := Equiv.refl α

instance : One (Project α) where
  one := one

instance : Inhabited (Project α) where
  default := 1

@[simp] lemma one_wager : (1 : Project α).wager = 0 := rfl

lemma one_plot : (1 : Project α).plot = Equiv.refl α := rfl

def mul (𝔞 𝔟 : Project α) : Project α where
  wager := 𝔞.wager + 𝔟.wager
  plot := 𝔞.plot.trans 𝔟.plot

instance : Mul (Project α) where
  mul := mul

@[simp] lemma mul_wager (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).wager = 𝔞.wager + 𝔟.wager := rfl

lemma mul_plot (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).plot = 𝔞.plot.trans 𝔟.plot := rfl

@[simp] lemma mul_one (𝔞 : Project α) : 𝔞 * 1 = 𝔞 := by
  ext <;> simp [mul_plot, one_plot]

@[simp] lemma mul_assoc (𝔞 𝔟 𝔠 : Project α) :
    (𝔞 * 𝔟) * 𝔠 = 𝔞 * (𝔟 * 𝔠) := by
  ext <;> simp [mul_plot, add_assoc, Equiv.trans_assoc]

def delocate (𝔞 : Project α) (φ : α ≃ β) : Project β where
  wager := 𝔞.wager
  plot := φ.symm.trans (𝔞.plot.trans φ)

@[simp] lemma delocate_wager (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).wager = 𝔞.wager := rfl

lemma delocate_plot (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).plot = φ.symm.trans (𝔞.plot.trans φ) := rfl

end Project

/-! #### Measurement and polarity -/

def Project.cycles [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : (Fintype.card α).Partition :=
  (𝔞 * 𝔟).plot.partition

def Project.measurement [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : ℕ :=
  𝔞.wager + 𝔟.wager + (𝔞.cycles 𝔟).parts.card

scoped notation "⟪" 𝔞 " | " 𝔟 "⟫" => Project.measurement 𝔞 𝔟

def Project.IsPolar [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : Prop :=
  0 < ⟪𝔞 | 𝔟⟫

scoped infix:50 " ⟂ " => Project.IsPolar

namespace Project

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma cycles_comm (𝔞 𝔟 : Project α) :
    𝔞.cycles 𝔟 = 𝔟.cycles 𝔞 := by
  apply Equiv.Perm.partition_eq_of_isConj.mp
  rw [isConj_iff]
  refine ⟨𝔞.plot, ?_⟩
  change 𝔞.plot * (𝔟.plot * 𝔞.plot) * 𝔞.plot⁻¹ = 𝔞.plot * 𝔟.plot
  group

lemma measurement_comm (𝔞 𝔟 : Project α) :
    ⟪𝔞 | 𝔟⟫ = ⟪𝔟 | 𝔞⟫ := by
  simp [Project.measurement, cycles_comm]
  grind

@[symm] lemma isPolar_symm {𝔞 𝔟 : Project α} :
    𝔞 ⟂ 𝔟 ↔ 𝔟 ⟂ 𝔞 := by
  simp [Project.IsPolar, measurement_comm]

/-! #### Projects -/

def fax (α : Type*) : Project (α ⊕ α) where
  wager := 0
  plot := Equiv.sumComm α α

@[simp] lemma fax_wager (α : Type*) : (fax α).wager = 0 := rfl

@[simp] lemma measurement_fax_one : ⟪fax α | 1⟫ = Fintype.card α := by
  suffices h : (Equiv.Perm.partition (Equiv.sumComm α α)).parts.card = Fintype.card α by
    simpa [Project.measurement, Project.cycles, fax] using h
  have hsupp : Equiv.Perm.support (Equiv.sumComm α α) = Finset.univ := by
    ext (_ | _) <;> simp [Equiv.Perm.mem_support]
  have hpow : (Equiv.sumComm α α : Equiv.Perm (α ⊕ α)) ^ 2 = 1 := by
    ext (_ | _) <;> rfl
  have hsum := Equiv.Perm.sum_cycleType (Equiv.sumComm α α)
  rw [Equiv.Perm.cycleType_of_pow_prime_eq_one hpow] at hsum
  simp_all [Equiv.Perm.parts_partition, Multiset.sum_replicate, Nat.mul_two]
  grind

@[simp] lemma fax_polar_one [Nonempty α] : fax α ⟂ 1 := by
  simpa [Project.IsPolar, measurement_fax_one, Fintype.card_pos_iff]

def daimon (r : ℕ) (α : Type*) : Project α where
  wager := r
  plot := Equiv.refl α

end Project

end GoI

end LO.Propositional.LinearLogic.Multiplicative
