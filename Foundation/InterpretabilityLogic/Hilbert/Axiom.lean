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
  mem_K : Modal.Axioms.K (.atom p) (.atom q) ∈ Ax := by grind;

class HasL where
  p : α
  mem_L : Modal.Axioms.L (.atom p) ∈ Ax := by grind;

class HasJ1 where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_J1 : InterpretabilityLogic.Axioms.J1 (.atom p) (.atom q) ∈ Ax := by grind;

class HasJ2 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J2 : InterpretabilityLogic.Axioms.J2 (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;

class HasJ2Plus where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J2Plus : InterpretabilityLogic.Axioms.J2Plus (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;

class HasJ3 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J3 : InterpretabilityLogic.Axioms.J3 (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;

class HasJ4 where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_J4 : InterpretabilityLogic.Axioms.J4 (.atom p) (.atom q) ∈ Ax := by grind;

class HasJ4Plus where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_J4Plus : InterpretabilityLogic.Axioms.J4Plus (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;

class HasJ5 where
  p : α
  mem_J5 : InterpretabilityLogic.Axioms.J5 (.atom p) ∈ Ax := by grind;

class HasJ6 where
  p : α
  mem_J6 : InterpretabilityLogic.Axioms.J6 (.atom p) ∈ Ax := by grind;

end Axiom

end LO.InterpretabilityLogic
