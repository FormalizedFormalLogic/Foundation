module

public import Foundation.LinearLogic.MELL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Geometry of Interaction (GoI I, 1989) for propositional $\mathbf{MELL}$
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.MultiplicativeExponential

class GoI (R : Type*) [Semiring R] [StarRing R] where
  left : R
  left_unitary : (star left) * left = 1
  right : R
  right_unitary : (star right) * right = 1
  left_right_disjoint : (star left) * right = 0
  right_left_disjoint : (star right) * left = 0
  internalTensor : R × R ≃+ R
  normal : internalTensor (1, 1) = 1
  star_internalTensor :
    star (internalTensor (x, y)) = internalTensor (star x, star y)
  mul_internalTensor :
    internalTensor (x, y) * internalTensor (z, w) = internalTensor (x * z, y * w)
  symmetry : R
  symmetry_isSelfAdjoint : IsSelfAdjoint symmetry
  symmetry_unitary : symmetry * symmetry = 1
  symmetry_symm :
    symmetry * internalTensor (x, y) = internalTensor (y, x) * symmetry
  trans : R
  trans_unitary : (star trans) * trans = 1
  trans_internalTensor :
    trans * internalTensor (x, internalTensor (y, z)) = internalTensor (internalTensor (x, y), z) * trans

namespace GoI

variable {R : Type*} [Semiring R]

def IsPolar (x y : R) : Prop := IsNilpotent (x * y)

scoped infix :50 " ⟂ " => IsPolar

namespace IsPolar

@[symm] protected lemma symm {x y : R} : x ⟂ y ↔ y ⟂ x :=
  IsNilpotent.rotate_mul_iff

@[simp] lemma zero_left (x : R) : 0 ⟂ x := by
  simp [IsPolar]

end IsPolar

def polar (s : Set R) : Set R := { y | ∀ x ∈ s, x ⟂ y }

scoped postfix:max "ᗮ" => polar

lemma subset_bipolar (s : Set R) : s ⊆ sᗮᗮ := by
  intro x hx y hy
  exact IsPolar.symm.mp (hy x hx)

/-- A _weak type_ is a bipolar set of operators -/
def IsWeakType (s : Set R) : Prop := sᗮᗮ = s

@[simp] lemma polar_isWeakType (s : Set R) : IsWeakType sᗮ := by
  apply Set.Subset.antisymm
  · intro x hx y hy
    exact hx y (subset_bipolar s hy)
  · exact subset_bipolar sᗮ

structure WeakType where
  carrier : Set R
  is_weak_type : IsWeakType carrier

variable [StarRing R] [GoI R]

abbrev itensor (x y : R) : R := internalTensor (x, y)

scoped infix:50 " ⨀ " => itensor

end GoI

end LO.Propositional.LinearLogic.MultiplicativeExponential
