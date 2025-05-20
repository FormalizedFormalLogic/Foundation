import Foundation.Modal.LogicSymbol

-- TODO: move to `LO.Axioms.Modal`

namespace LO.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)

/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality := ◇φ ⭤ ∼(□(∼φ))

protected abbrev K := □(φ ➝ ψ) ➝ □φ ➝ □ψ

/-- Axiom for reflexive -/
protected abbrev T := □φ ➝ φ

/-- Alternative axiom `T` -/
protected abbrev DiaTc := φ ➝ ◇φ

/-- Axiom for symmetric -/
protected abbrev B := φ ➝ □◇φ

/-- Axiom for serial -/
protected abbrev D := □φ ➝ ◇φ

/-- Alternative axiom `D` -/
protected abbrev P : F := ∼(□⊥)

/-- Axiom for transivity -/
protected abbrev Four := □φ ➝ □□φ

/-- Axiom for euclidean -/
protected abbrev Five := ◇φ ➝ □◇φ

/-- Axiom for confluency -/
protected abbrev Point2 := ◇□φ ➝ □◇φ

/-- Axiom for weak confluency -/
protected abbrev WeakPoint2 := ◇(□φ ⋏ ψ) ➝ □(◇φ ⋎ ψ)

/-- Axiom for density -/
protected abbrev C4 := □□φ ➝ □φ

/-- Axiom for functionality -/
protected abbrev CD := ◇φ ➝ □φ

/-- Axiom for coreflexivity -/
protected abbrev Tc := φ ➝ □φ

/-- Alternative axiom `Tc` -/
protected abbrev DiaT := ◇φ ➝ φ

/-- Axiom for isolated -/
protected abbrev Ver := □φ

/-- Axiom for connectivity -/
protected abbrev Point3 := □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ)

/-- Axiom for weak connectivity -/
protected abbrev WeakPoint3 := □(⊡φ ➝ ψ) ⋎ □(⊡ψ ➝ φ)

/--
  Axiom for
  - weakly converse wellfounded partial order (for non-resritcted Kripke frame)
  - partial order (for finite Kripke frame)
-/
protected abbrev Grz := □(□(φ ➝ □φ) ➝ φ) ➝ φ

/--
  Axiom for McKinsey condition
-/
protected abbrev M := (□◇φ ➝ ◇□φ)

/--
  Axiom for
  - transitive converse wellfounded order (for non-resritcted Kripke frame)
  - strict partial order (for finite Kripke frame)
-/
protected abbrev L := □(□φ ➝ φ) ➝ □φ

protected abbrev H := □(□φ ⭤ φ) ➝ □φ

protected abbrev Z := □(□φ ➝ φ) ➝ (◇□φ ➝ □φ)

end LO.Axioms


namespace LO.Axioms.Modal

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Mk := □φ ⋏ ψ ➝ ◇(□□φ ⋏ ◇ψ)

end LO.Axioms.Modal
