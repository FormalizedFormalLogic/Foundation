/-
  Naming of axioms are refered from:

  - 1988, A. Visser, "Preliminary Notes on Interpretability Logic"
  - 1991, V. Švejdar, "Some independence results in interpretability logic"
  - 1997, A. Visser, "An Overview of Interpretability Logic"
  - 2011, E. Goris, J. J. Joosten, "A New Principle in the Interpretability Logic of  all Reasonable Arithmetical Theories"
  - 2021, T. Kurahashi, Y. Okawa, "Modal completeness of sublogics of the  interpretability logic IL"
  - 2022, L. Mitec, "On Logics and Semantics of Interpretability"
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
protected abbrev P₀ := (φ ➝ ◇ψ) ➝ □(φ ▷ ψ)

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
  - Visser 1997, `M₀`
-/
protected abbrev M₀ := (φ ▷ ψ) ➝ (◇φ ⋏ □χ) ▷ (ψ ⋏ □χ)

/--
  - Visser 1988, `J6`: De Jongh-Visser Principle
  - Švejdar 1991, `W`
-/
protected abbrev W := (φ ▷ ψ) ➝ (φ ▷ (ψ ⋏ □(∼φ)))

/--
  - Visser 1997, `W*`
-/
protected abbrev WStar := (φ ▷ ψ) ➝ ((ψ ⋏ □χ) ▷ (ψ ⋏ □χ ⋏ □(∼φ)))

/--
  - Švejdar 1991, `KW1`
  - Visser 1997, `KW1`
-/
protected abbrev KW1 := (φ ▷ ◇⊤) ➝ (⊤ ▷ ∼φ)

/--
  - Švejdar 1991, `KW1⁰`
-/
protected abbrev KW1₀ := (φ ▷ ◇⊤) ➝ (⊤ ▷ (∼φ ⋏ □(∼φ)))

/--
  - Visser 1997, `KW2`
-/
protected abbrev KW2 := φ ▷ ◇ψ ➝ ψ ▷ (ψ ⋏ ∼φ)

/--
  - Visser 1997, `KW3`
-/
protected abbrev KW3 := φ ▷ (ψ ⋎ ◇φ) ➝ φ ▷ ψ

/--
  - Visser 1997, `KW4`
-/
protected abbrev KW4 := φ ▷ ψ ➝ ψ ▷ (ψ ⋏ □(∼φ))


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
