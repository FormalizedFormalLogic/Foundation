import Foundation.InterpretabilityLogic.Formula.Substitution
import Foundation.Modal.Axioms
import Foundation.InterpretabilityLogic.Axioms

namespace LO.InterpretabilityLogic

variable {α : Type _}


abbrev Axiom (α) := Set (Formula α)

abbrev Axiom.instances (Ax : Axiom α) : FormulaSet α := { φ | ∃ ψ ∈ Ax, ∃ s, φ = ψ⟦s⟧ }

namespace Axiom

variable (Ax Ax₁ Ax₂ : Axiom α)

class HasK where
  p : α
  q : α
  ne_pq : p ≠ q := by simp;
  mem_K : Modal.Axioms.K (.atom p) (.atom q) ∈ Ax := by grind;

class HasL where
  p : α
  mem_L : Modal.Axioms.L (.atom p) ∈ Ax := by grind;


class HasJ1 where
  p : α
  q : α
  ne_pq : p ≠ q := by simp;
  mem_J1 : InterpretabilityLogic.Axioms.J1 (.atom p) (.atom q) ∈ Ax := by grind;
attribute [simp] HasJ1.ne_pq
export HasJ1 (mem_J1)
def HasJ1.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ1] : Ax₂.HasJ1 where
  p := HasJ1.p Ax₁;
  q := HasJ1.q Ax₁;
  mem_J1 := h mem_J1


class HasJ2 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by simp;
  ne_qr : q ≠ r := by simp;
  ne_rp : r ≠ p := by simp;
  mem_J2 : InterpretabilityLogic.Axioms.J2 (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;
attribute [simp] HasJ2.ne_pq HasJ2.ne_qr HasJ2.ne_rp
export HasJ2 (mem_J2)

def HasJ2.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ2] : Ax₂.HasJ2 where
  p := HasJ2.p Ax₁;
  q := HasJ2.q Ax₁;
  r := HasJ2.r Ax₁;
  mem_J2 := h mem_J2


class HasJ2Plus where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by simp;
  ne_qr : q ≠ r := by simp;
  ne_rp : r ≠ p := by simp;
  mem_J2Plus : InterpretabilityLogic.Axioms.J2Plus (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;
attribute [simp] HasJ2Plus.ne_pq HasJ2Plus.ne_qr HasJ2Plus.ne_rp
export HasJ2Plus (mem_J2Plus)

def HasJ2Plus.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ2Plus] : Ax₂.HasJ2Plus where
  p := HasJ2Plus.p Ax₁;
  q := HasJ2Plus.q Ax₁;
  r := HasJ2Plus.r Ax₁;
  mem_J2Plus := h mem_J2Plus


class HasJ3 where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by simp;
  ne_qr : q ≠ r := by simp;
  ne_rp : r ≠ p := by simp;
  mem_J3 : InterpretabilityLogic.Axioms.J3 (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;
attribute [simp] HasJ3.ne_pq HasJ3.ne_qr HasJ3.ne_rp
export HasJ3 (mem_J3)

def HasJ3.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ3] : Ax₂.HasJ3 where
  p := HasJ3.p Ax₁;
  q := HasJ3.q Ax₁;
  r := HasJ3.r Ax₁;
  mem_J3 := h mem_J3


class HasJ4 where
  p : α
  q : α
  ne_pq : p ≠ q := by simp;
  mem_J4 : InterpretabilityLogic.Axioms.J4 (.atom p) (.atom q) ∈ Ax := by grind;
attribute [simp] HasJ4.ne_pq
export HasJ4 (mem_J4)

def HasJ4.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ4] : Ax₂.HasJ4 where
  p := HasJ4.p Ax₁;
  q := HasJ4.q Ax₁;
  mem_J4 := h mem_J4


class HasJ4Plus where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by simp;
  ne_qr : q ≠ r := by simp;
  ne_rp : r ≠ p := by simp;
  mem_J4Plus : InterpretabilityLogic.Axioms.J4Plus (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;

attribute [simp] HasJ4Plus.ne_pq HasJ4Plus.ne_qr HasJ4Plus.ne_rp
export HasJ4Plus (mem_J4Plus)

def HasJ4Plus.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ4Plus] : Ax₂.HasJ4Plus where
  p := HasJ4Plus.p Ax₁;
  q := HasJ4Plus.q Ax₁;
  r := HasJ4Plus.r Ax₁;
  mem_J4Plus := h mem_J4Plus


class HasJ5 where
  p : α
  mem_J5 : InterpretabilityLogic.Axioms.J5 (.atom p) ∈ Ax := by grind;
export HasJ5 (mem_J5)

def HasJ5.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ5] : Ax₂.HasJ5 where
  p := HasJ5.p Ax₁;
  mem_J5 := h mem_J5


class HasJ6 where
  p : α
  mem_J6 : InterpretabilityLogic.Axioms.J6 (.atom p) ∈ Ax := by grind;
export HasJ6 (mem_J6)

def HasJ6.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasJ6] : Ax₂.HasJ6 where
  p := HasJ6.p Ax₁;
  mem_J6 := h mem_J6


class HasM where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by simp;
  ne_qr : q ≠ r := by simp;
  ne_rp : r ≠ p := by simp;
  mem_M : InterpretabilityLogic.Axioms.M (.atom p) (.atom q) (.atom r) ∈ Ax := by grind;
attribute [simp] HasM.ne_pq HasM.ne_qr HasM.ne_rp
export HasM (mem_M)

def HasM.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasM] : Ax₂.HasM where
  p := HasM.p Ax₁;
  q := HasM.q Ax₁;
  r := HasM.r Ax₁;
  mem_M := h mem_M


class HasP where
  p : α
  q : α
  ne_pq : p ≠ q := by simp;
  mem_P : InterpretabilityLogic.Axioms.P (.atom p) (.atom q) ∈ Ax := by grind;
attribute [simp] HasP.ne_pq
export HasP (mem_P)

def HasP.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasP] : Ax₂.HasP where
  p := HasP.p Ax₁;
  q := HasP.q Ax₁;
  mem_P := h mem_P


class HasW where
  p : α
  q : α
  ne_pq : p ≠ q := by simp;
  mem_W : InterpretabilityLogic.Axioms.W (.atom p) (.atom q) ∈ Ax := by grind;

attribute [simp] HasW.ne_pq
export HasW (mem_W)

def HasW.of_mem {Ax₁ Ax₂ : Axiom α} (h : Ax₁ ⊆ Ax₂) [Ax₁.HasW] : Ax₂.HasW where
  p := HasW.p Ax₁;
  q := HasW.q Ax₁;
  mem_W := h mem_W


end Axiom

section

-- TODO: too trivial, it should be proved by one `simp`.

open Formula (atom)

@[simp]
lemma ne_J1_J6 : Axioms.J1 (atom 0) (atom 1) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

@[simp]
lemma ne_J2_J6 : Axioms.J2 (atom 0) (atom 1) (atom 2) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

@[simp]
lemma ne_J2Plus_J6 : Axioms.J2Plus (atom 0) (atom 1) (atom 2) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

@[simp]
lemma ne_J4_J6 : Axioms.J4 (atom 0) (atom 1) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

@[simp]
lemma ne_J4Plus_J6 : Axioms.J4Plus (atom 0) (atom 1) (atom 2) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

@[simp]
lemma ne_J5_J6 : Axioms.J5 (atom 0) ≠ Axioms.J6 (atom 0) := by tauto;

@[simp]
lemma ne_M_J6 : Axioms.M (atom 0) (atom 1) (atom 2) ≠ Axioms.J6 (atom 0) := by
  apply Formula.imp_inj.not.mpr;
  simp;

end

end LO.InterpretabilityLogic
