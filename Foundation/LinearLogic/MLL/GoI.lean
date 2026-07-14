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
  ⟪𝔞 | 𝔟⟫ = 1

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

@[symm, grind =] lemma isPolar_symm {𝔞 𝔟 : Project α} :
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

def daimon (r : ℕ) (α : Type*) : Project α where
  wager := r
  plot := Equiv.refl α

end Project

/-! ### Polarity and Conduct -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def poler (A : Set (Project α)) : Set (Project α) :=
  {𝔟 | ∀ 𝔞 ∈ A, 𝔞 ⟂ 𝔟}

scoped postfix:max "ᗮ" => poler

def IsConduct (A : Set (Project α)) : Prop :=
  A = Aᗮᗮ

structure Conduct (α : Type*) [Fintype α] [DecidableEq α] where
  set : Set (Project α)
  set_isConduct : IsConduct set

instance : SetLike (Conduct α) (Project α) where
  coe := Conduct.set
  coe_injective p q h := by cases p; cases q; congr

@[simp] lemma mem_poler_iff (A : Set (Project α)) (𝔟 : Project α) :
    𝔟 ∈ Aᗮ ↔ ∀ 𝔞 ∈ A, 𝔞 ⟂ 𝔟 := by rfl

@[simp] lemma tripoler_eq_poler (A : Set (Project α)) : Aᗮᗮᗮ = Aᗮ := by
  ext 𝔟; simp; grind

@[simp] lemma subset_bipoler (A : Set (Project α)) : A ⊆ Aᗮᗮ := by
  intro 𝔞 h𝔞; simp; grind

lemma isConduct_iff_subset_bipoler {A : Set (Project α)} : IsConduct A ↔ Aᗮᗮ ⊆ A := by
  simp [IsConduct, subset_antisymm_iff]

@[simp] lemma poler_isConduct (A : Set (Project α)) : IsConduct Aᗮ := by
  simp [IsConduct]

namespace Conduct

def tensor (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ A, ∃ 𝔟 ∈ B, 𝔠 = 𝔞 + 𝔟}ᗮᗮ
  set_isConduct := by simp

def par (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ Aᗮ, ∃ 𝔟 ∈ Bᗮ, 𝔠 = 𝔞 + 𝔟}ᗮ
  set_isConduct := by simp

end Conduct

/-! ### Successful Project -/

structure Project.IsSuccessful (𝔞 : Project α) : Prop where
  square_eq_one : 𝔞 * 𝔞 = 1
  trace_zero : 𝔞.plot.support = Finset.univ

def Conduct.IsSuccessful (A : Conduct α) : Prop :=
  ∃ 𝔞 ∈ A, 𝔞.IsSuccessful

end GoI

end LO.Propositional.LinearLogic.Multiplicative
