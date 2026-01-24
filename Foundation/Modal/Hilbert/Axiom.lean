import Foundation.Modal.Axioms
import Foundation.Modal.Formula.Basic

namespace LO.Modal

variable {α : Type _}

abbrev Axiom (α) := Set (Formula α)

abbrev Axiom.instances (Ax : Axiom α) : FormulaSet α := { φ | ∃ ψ ∈ Ax, ∃ s, φ = ψ⟦s⟧ }

@[grind =>]
lemma Axiom.of_mem {Ax : Axiom α} {φ : Formula α} (hφ : φ ∈ Ax) : φ⟦s⟧ ∈ Ax.instances := by
  dsimp [Axiom.instances];
  use φ;
  constructor;
  . assumption;
  . grind;

namespace Axiom

class HasM (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_m : Axioms.M (.atom p) (.atom q) ∈ Ax := by tauto;

class HasC (Ax : Axiom α)  where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_c : Axioms.C (.atom p) (.atom q) ∈ Ax := by tauto;

class HasN (Ax : Axiom α)  where
  mem_n : Axioms.N ∈ Ax := by tauto;

class HasK (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ Ax := by tauto;

class HasT (Ax : Axiom α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ Ax := by tauto;

class HasD (Ax : Axiom α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ Ax := by tauto

class HasP (Ax : Axiom α) where
  mem_P : Axioms.P ∈ Ax := by tauto;

class HasB (Ax : Axiom α) where
  p : α
  mem_B : Axioms.B (.atom p) ∈ Ax := by tauto;

class HasFour (Ax : Axiom α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ Ax := by tauto;

class HasFourN (n : ℕ) (Ax : Axiom α) where
  p : α
  mem_FourN : Axioms.FourN n (.atom p) ∈ Ax := by tauto;

class HasFive (Ax : Axiom α) where
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ Ax := by tauto;

class HasPoint2 (Ax : Axiom α) where
  p : α
  mem_Point2 : Axioms.Point2 (.atom p) ∈ Ax := by tauto;

class HasWeakPoint2 (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint2 : Axioms.WeakPoint2 (.atom p) (.atom q) ∈ Ax := by tauto;

class HasPoint3 (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Point3 : Axioms.Point3 (.atom p) (.atom q) ∈ Ax := by tauto;

class HasWeakPoint3 (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint3 : Axioms.WeakPoint3 (.atom p) (.atom q) ∈ Ax := by tauto;

class HasPoint4 (Ax : Axiom α) where
  p : α
  mem_Point4 : Axioms.Point4 (.atom p) ∈ Ax := by tauto;

class HasL (Ax : Axiom α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ Ax := by tauto;

class HasZ (Ax : Axiom α) where
  p : α
  mem_Z : Axioms.Z (.atom p) ∈ Ax := by tauto;

class HasGrz (Ax : Axiom α) where
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ Ax := by tauto;

class HasDum (Ax : Axiom α) where
  p : α
  mem_Dum : Axioms.Dum (.atom p) ∈ Ax := by tauto;

class HasTc (Ax : Axiom α) where
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ Ax := by tauto;

class HasVer (Ax : Axiom α) where
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ Ax := by tauto;

class HasHen (Ax : Axiom α) where
  p : α
  mem_Hen : Axioms.Hen (.atom p) ∈ Ax := by tauto;

class HasMcK (Ax : Axiom α) where
  p : α
  mem_McK : Axioms.McK (.atom p) ∈ Ax := by tauto;

class HasMk (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Mk : Axioms.Mk (.atom p) (.atom q) ∈ Ax := by tauto;

class HasH1 (Ax : Axiom α) where
  p : α
  mem_H1 : Axioms.H (.atom p) ∈ Ax := by tauto;

class HasGeach (g) (Ax : Axiom α) where
  p : α
  mem_Geach : Axioms.Geach g (.atom p) ∈ Ax := by tauto;

end Axiom

end LO.Modal
