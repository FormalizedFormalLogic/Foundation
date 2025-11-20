
import Foundation.Propositional.Formula
import Foundation.Propositional.Entailment.Cl.Basic
import Foundation.Propositional.Entailment.KrieselPutnam
import Foundation.Propositional.Entailment.Scott
import Foundation.Propositional.Entailment.Corsi

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
  mem_lem : Axioms.WLEM (.atom p) ∈ Ax := by tauto;

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


class HasAxiomRfl (Ax : Axiom α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_rfl : Axioms.Rfl #p #q ∈ Ax := by tauto;
attribute [simp] HasAxiomRfl.ne_pq


class HasAxiomTra1 (Ax : Axiom α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_tra1 : Axioms.Tra1 #p #q #r ∈ Ax := by grind;
attribute [simp] HasAxiomTra1.ne_pq HasAxiomTra1.ne_qr HasAxiomTra1.ne_rp


class HasAxiomTra2 (Ax : Axiom α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by trivial;
  ne_qr : q ≠ r := by trivial;
  ne_rp : r ≠ p := by trivial;
  mem_tra2 : Axioms.Tra2 #p #q #r ∈ Ax := by grind;
attribute [simp] HasAxiomTra2.ne_pq HasAxiomTra2.ne_qr HasAxiomTra2.ne_rp


end Axiom

end LO.Propositional
