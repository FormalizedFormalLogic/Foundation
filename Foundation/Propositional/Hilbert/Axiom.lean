import Foundation.Propositional.Axioms
import Foundation.Propositional.Formula
import Foundation.Logic.Axioms

namespace LO.Propositional

variable {α : Type _}

abbrev Axiom (α) := Set (Formula α)

abbrev Axiom.instances (Ax : Axiom α) : FormulaSet α := { φ | ∃ ψ ∈ Ax, ∃ s, φ = ψ⟦s⟧ }

namespace Axiom

class HasEFQ (Ax : Axiom α) where
  p : α
  mem_efq : Axioms.EFQ (.atom p) ∈ Ax := by tauto;

class HasLEM (Ax : Axiom α) where
  p : α
  mem_lem : Axioms.LEM (.atom p) ∈ Ax := by tauto;

class HasWLEM (Ax : Axiom α) where
  p : α
  mem_lem : Axioms.WeakLEM (.atom p) ∈ Ax := by tauto;

class HasDummett (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_m : Axioms.Dummett (.atom p) (.atom q) ∈ Ax := by tauto;

class HasPeirce (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_peirce : Axioms.Peirce (.atom p) (.atom q) ∈ Ax := by tauto;

class HasKrieselPutnam (Ax : Axiom α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_kriesel_putnam : Axioms.KrieselPutnam (.atom p) (.atom q) (.atom r) ∈ Ax := by tauto;

class HasScott (Ax : Axiom α) where
  p : α
  mem_scott : Axioms.Scott (.atom p) ∈ Ax := by tauto;

end Axiom

end LO.Propositional
