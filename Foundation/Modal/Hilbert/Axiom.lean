import Foundation.Modal.Axioms
import Foundation.Modal.Formula

namespace LO.Modal

variable {α : Type _}

abbrev Axiom (α) := Set (Formula α)

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

class HasFour (Ax : Axiom α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ Ax := by tauto;

end Axiom

end LO.Modal
