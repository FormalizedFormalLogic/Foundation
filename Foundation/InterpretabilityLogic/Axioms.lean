/-
  Naming of axioms are refered from:

  - T. Kurahashi, Y. Okawa, 2021, "Modal completeness of sublogics of the  interpretability logic IL"
  - A. Visser, 1988, "Preliminary Notes on Interpretability Logic"
  - V. Švejdar, 1991, "Some independence results in interpretability logic"
  - L. Mitec, 2022, "On Logics and Semantics of Interpretability"
  - E. Goris, J. J. Joosten, 2011, "A New Principle in the Interpretability Logic of  all Reasonable Arithmetical Theories"
-/
import Foundation.InterpretabilityLogic.LogicSymbol

namespace LO.InterpretabilityLogic.Axioms

variable {F : Type*} [InterpretabilityLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev J1 := □(φ ➝ ψ) ➝ (φ ▷ ψ)

protected abbrev J1' := (φ ▷ φ)


protected abbrev J2 := (φ ▷ ψ) ➝ (ψ ▷ χ) ➝ (φ ▷ χ)

protected abbrev J2Plus := (φ ▷ (ψ ⋎ χ)) ➝ (ψ ▷ χ) ➝ (φ ▷ χ)

protected abbrev J2Plus' := (φ ▷ ψ) ➝ ((ψ ⋏ ∼χ) ▷ χ) ➝ (φ ▷ χ)


protected abbrev J3 := (φ ▷ χ) ➝ (ψ ▷ χ) ➝ ((φ ⋎ ψ) ▷ χ)


protected abbrev J4 := (φ ▷ ψ) ➝ (◇φ ➝ ◇ψ)

/--
  - Visser 1988, `K2`
-/
protected abbrev J4' := (φ ▷ ψ) ➝ ((ψ ▷ ⊥) ➝ (φ ▷ ⊥))

/--
  - Visser 1988, `K1`
-/
protected abbrev J4Plus := □(φ ➝ ψ) ➝ (χ ▷ φ ➝ χ ▷ ψ)

protected abbrev J4Plus' := □φ ➝ (χ ▷ (φ ➝ ψ) ➝ χ ▷ ψ)

protected abbrev J4Plus'' := □φ ➝ (χ ▷ ψ ➝ χ ▷ (φ ⋏ ψ))


protected abbrev J5 := ◇φ ▷ φ

protected abbrev J6 := □φ ⭤ (∼φ ▷ ⊥)

/--
  Persistency Principle
  - Visser 1988, `J7`
-/
protected abbrev P := (φ ▷ ψ) ➝ □(φ ▷ ψ)

/--
  - Goris & Joosten 2011, `P₀`
-/
protected abbrev P0 := (φ ➝ ◇ψ) ➝ □(φ ▷ ψ)

/--
  Montagna's Principle
  - Visser 1988, `J8`
-/
protected abbrev M := (φ ▷ ψ) ➝ ((φ ⋏ □χ) ▷ (ψ ⋏ □χ))

/--
  - Visser 1988, `K12`
  - Švejdar 1991, `KM1`
-/
protected abbrev KM1 := (φ ▷ ◇ψ) ➝ □(φ ➝ ◇ψ)

/--
  - Mitec 2022, `M₀`
-/
protected abbrev M0 := (φ ▷ ψ) ➝ (◇φ ⋏ □χ ➝ ψ ⋏ □χ)

/--
  - Visser 1988, `J6`: De Jongh-Visser Principle
  - Švejdar 1991, `W`
-/
protected abbrev W := (φ ▷ ψ) ➝ (φ ▷ (ψ ⋏ □(∼φ)))

protected abbrev WStar := (φ ▷ ψ) ➝ ((ψ ⋏ □χ) ▷ (ψ ⋏ □χ ⋏ □(∼φ)))

/--
  - Švejdar 1991, `KW1`
-/
protected abbrev KW1 := (φ ▷ ◇⊤) ➝ (⊤ ▷ ∼φ)

/--
  - Švejdar 1991, `KW1⁰`
-/
protected abbrev KW1_0 := (φ ▷ ◇⊤) ➝ (⊤ ▷ (∼φ ⋏ □(∼φ)))

/--
  Feferman's Principle

  - Švejdar 1991, `F`
-/
protected abbrev F := (φ ▷ ◇φ) ➝ □(∼φ)

/--
  - Visser 1988, `K13`: Relative Interpretability Implies Provable Relative Consistency

  Note: `P ⊢ RIIPRC` in Visser 1988 Section 16.4
-/
protected abbrev RIIPRC := φ ▷ ψ ➝ □(◇φ ➝ ◇ψ)

end LO.InterpretabilityLogic.Axioms
