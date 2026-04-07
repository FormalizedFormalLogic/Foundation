module

public import Foundation.Modal.LogicSymbol

@[expose]
public section

namespace LO.Modal.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)

/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality := ◇φ 🡘 ∼(□(∼φ))

protected abbrev K := □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ

protected abbrev M := □(φ ⋏ ψ) 🡒 (□φ ⋏ □ψ)

protected abbrev C := (□φ ⋏ □ψ) 🡒 □(φ ⋏ ψ)

protected abbrev N := □(⊤ : F)

/-- Axiom for reflexive -/
protected abbrev T := □φ 🡒 φ

/-- Alternative axiom `T` -/
protected abbrev DiaTc := φ 🡒 ◇φ

/-- Axiom for symmetric -/
protected abbrev B := φ 🡒 □◇φ

/-- Axiom for serial -/
protected abbrev D := □φ 🡒 ◇φ

/-- Alternative axiom `D` -/
protected abbrev P : F := ∼(□⊥)

/-- Axiom for transivity -/
protected abbrev Four := □φ 🡒 □□φ

protected abbrev FourN (n : ℕ) (φ : F) := □^[n]φ 🡒 □^[(n + 1)]φ

/-- Axiom for euclidean -/
protected abbrev Five := ◇φ 🡒 □◇φ

/-- Axiom for confluency -/
protected abbrev Point2 := ◇□φ 🡒 □◇φ

/-- Axiom for weak confluency -/
protected abbrev WeakPoint2 := ◇(□φ ⋏ ψ) 🡒 □(◇φ ⋎ ψ)

/-- Axiom for density -/
protected abbrev C4 := □□φ 🡒 □φ

/-- Axiom for functionality -/
protected abbrev CD := ◇φ 🡒 □φ

/-- Axiom for coreflexivity -/
protected abbrev Tc := φ 🡒 □φ

/-- Alternative axiom `Tc` -/
protected abbrev DiaT := ◇φ 🡒 φ

/-- Axiom for isolated -/
protected abbrev Ver := □φ

/-- Axiom for connectivity -/
protected abbrev Point3 := □(□φ 🡒 ψ) ⋎ □(□ψ 🡒 φ)

/-- Axiom for weak connectivity -/
protected abbrev WeakPoint3 := □(⊡φ 🡒 ψ) ⋎ □(⊡ψ 🡒 φ)

/--
  - `R1`: Hudges & Cresswell
-/
protected abbrev Point4 := ◇□φ 🡒 φ 🡒 □φ

/--
  Axiom for
  - weakly converse wellfounded partial order (for non-resritcted Kripke frame)
  - partial order (for finite Kripke frame)
-/
protected abbrev Grz := □(□(φ 🡒 □φ) 🡒 φ) 🡒 φ

protected abbrev Dum := □(□(φ 🡒 □φ) 🡒 φ) 🡒 (◇□φ 🡒 φ)

/--
  Axiom for McKinsey condition
-/
protected abbrev McK := □◇φ 🡒 ◇□φ

/--
  Axiom for
  - transitive converse wellfounded order (for non-resritcted Kripke frame)
  - strict partial order (for finite Kripke frame)
-/
protected abbrev L := □(□φ 🡒 φ) 🡒 □φ

protected abbrev Z := □(□φ 🡒 φ) 🡒 (◇□φ 🡒 □φ)

protected abbrev Hen := □(□φ 🡘 φ) 🡒 □φ

protected abbrev Mk := □φ ⋏ ψ 🡒 ◇(□□φ ⋏ ◇ψ)

/--
  For Sobocinski's `K1.2`.
-/
protected abbrev H := φ 🡒 □(◇φ 🡒 φ)

protected structure Geach.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

/--
  Axiom for Geach confluency.
-/
protected abbrev Geach (g : Geach.Taple) (φ : F) := (◇^[g.i](□^[g.m]φ)) 🡒 (□^[g.j](◇^[g.n]φ))

/--
  Section 13 in Boolos 1994
-/
protected abbrev I := □(□φ 🡒 □ψ) ⋎ □(□ψ 🡒 ⊡φ)

end LO.Modal.Axioms

end
