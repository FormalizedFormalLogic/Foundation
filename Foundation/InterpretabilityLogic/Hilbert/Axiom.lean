import Foundation.InterpretabilityLogic.Formula.Substitution
import Foundation.Modal.Axioms
import Foundation.InterpretabilityLogic.Axioms

namespace LO.InterpretabilityLogic

variable {α : Type _}

abbrev Axiom (α) := Set (Formula α)

abbrev Axiom.instances (Ax : Axiom α) : FormulaSet α := { φ | ∃ ψ ∈ Ax, ∃ s, φ = ψ⟦s⟧ }

namespace Axiom

variable (Ax : Axiom α)

class HasK where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Modal.Axioms.K (.atom p) (.atom q) ∈ Ax := by tauto;

class HasL where
  p : α
  mem_L : Modal.Axioms.L (.atom p) ∈ Ax := by tauto;

class HasJ1 where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_J1 : InterpretabilityLogic.Axioms.J1 (.atom p) (.atom q) ∈ Ax := by tauto;

class HasJ2 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J2 : InterpretabilityLogic.Axioms.J2 (.atom p) (.atom q) (.atom r) ∈ Ax := by tauto;

class HasJ3 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J3 : InterpretabilityLogic.Axioms.J3 (.atom p) (.atom q) (.atom r) ∈ Ax := by tauto;

class HasJ4 where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_J4 : InterpretabilityLogic.Axioms.J4 (.atom p) (.atom q) ∈ Ax := by tauto;

class HasJ5 where
  p : α
  mem_J5 : InterpretabilityLogic.Axioms.J5 (.atom p) ∈ Ax := by tauto;

end Axiom

end LO.InterpretabilityLogic
