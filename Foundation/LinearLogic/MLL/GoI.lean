module

public import Foundation.LinearLogic.MLL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Geometry of Interaction (GoI I, 1989) for $\mathbf{MLL}$
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.Multiplicative

class GoI (R : Type*) [Semiring R] [StarRing R] where
  left : R
  left_total : (star left) * left = 1
  right : R
  right_total : (star right) * right = 1
  left_right_disjoint_range : (star left) * right = 0
  right_left_disjoint_range : (star right) * left = 0

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

variable (R)

structure WeakType where
  set : Set R
  is_weak_type : IsWeakType set := by simp

variable {R}

namespace WeakType

instance : SetLike (WeakType R) R where
  coe := WeakType.set
  coe_injective A B := by rcases A; rcases B; simp

end WeakType

variable [StarRing R] [GoI R]

def opTensor (x y : R) : R :=
  left * x * (star left) + right * y * (star right)

def WeakType.tensor (A B : WeakType R) : WeakType R where
  set := (Set.image2 opTensor A.set B.set)ᗮᗮ

def WeakType.par (A B : WeakType R) : WeakType R where
  set := (Set.image2 opTensor A.setᗮ B.setᗮ)ᗮ

instance : Tensor (WeakType R) where
  tensor := WeakType.tensor

instance : Par (WeakType R) where
  par := WeakType.par

end GoI

end LO.Propositional.LinearLogic.Multiplicative
