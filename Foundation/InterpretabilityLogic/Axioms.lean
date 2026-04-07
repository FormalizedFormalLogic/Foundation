module

/-
  Naming of axioms are refered from:

  - Goris & Joosten, "A New Principle in the Interpretability Logic of  all Reasonable Arithmetical Theories" [G.J11]
  - Goris & Joosten, "Modal Matters in Interpretability Logics" [G.J08]
  - Goris & Visser, "How to Derive Principles of Interpretability Logic A Toolkit" [G.V04]
  - Kurahashi & Okawa, "Modal completeness of sublogics of the  interpretability logic IL" [K.O21]
  - Mitec, "On Logics and Semantics of Interpretability" [Mit22]
  - Švejdar, "Some independence results in interpretability logic" [Sve91]
  - Visser, "An Overview of Interpretability Logic" [Vis97]
  - Visser, "Preliminary Notes on Interpretability Logic" [Vis88]
-/
public import Foundation.InterpretabilityLogic.LogicSymbol

@[expose] public section

namespace LO.InterpretabilityLogic.Axioms

variable {F : Type*} [InterpretabilityLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev J1 := □(φ 🡒 ψ) 🡒 (φ ▷ ψ)

protected abbrev J1' := (φ ▷ φ)


protected abbrev J2 := (φ ▷ ψ) 🡒 (ψ ▷ χ) 🡒 (φ ▷ χ)

protected abbrev J2Plus := (φ ▷ (ψ ⋎ χ)) 🡒 (ψ ▷ χ) 🡒 (φ ▷ χ)

protected abbrev J2Plus' := (φ ▷ ψ) 🡒 ((ψ ⋏ ∼χ) ▷ χ) 🡒 (φ ▷ χ)


protected abbrev J3 := (φ ▷ χ) 🡒 (ψ ▷ χ) 🡒 ((φ ⋎ ψ) ▷ χ)


protected abbrev J4 := (φ ▷ ψ) 🡒 (◇φ 🡒 ◇ψ)

/--
  - `K2` in [Vis88]
-/
protected abbrev J4' := (φ ▷ ψ) 🡒 ((ψ ▷ ⊥) 🡒 (φ ▷ ⊥))

/--
  - `K1` in [Vis88]
-/
protected abbrev J4Plus := □(φ 🡒 ψ) 🡒 (χ ▷ φ 🡒 χ ▷ ψ)

protected abbrev J4Plus' := □φ 🡒 (χ ▷ (φ 🡒 ψ) 🡒 χ ▷ ψ)

protected abbrev J4Plus'' := □φ 🡒 (χ ▷ ψ 🡒 χ ▷ (φ ⋏ ψ))


protected abbrev J5 := ◇φ ▷ φ

protected abbrev J6 := □φ 🡘 (∼φ ▷ ⊥)

/--
  Persistency Principle
  - `J7` in [Vis88]
-/
protected abbrev P := (φ ▷ ψ) 🡒 □(φ ▷ ψ)

/--
  - `P₀` in [G.J08]
-/
protected abbrev P₀ := (φ ▷ ◇ψ) 🡒 □(φ ▷ ψ)

/--
  Montagna's Principle
  - `J8` in [Vis88]
-/
protected abbrev M := (φ ▷ ψ) 🡒 ((φ ⋏ □χ) ▷ (ψ ⋏ □χ))

/--
  - `K12` in [Vis88]
  - `KM1` in [Sve91]
-/
protected abbrev KM1 := (φ ▷ ◇ψ) 🡒 □(φ 🡒 ◇ψ)

/--
  - `M₀` in [Vis97]
-/
protected abbrev M₀ := (φ ▷ ψ) 🡒 (◇φ ⋏ □χ) ▷ (ψ ⋏ □χ)

/--
  - `M₀*` in [G.J08]
-/
protected abbrev M₀Star := (φ ▷ ψ) 🡒 (◇φ ⋏ □χ) ▷ (ψ ⋏ □χ ⋏ □(∼φ))

/--
  - `J6` in [Vis88]: De Jongh-Visser Principle
  - `W` in [Sve91]
-/
protected abbrev W := (φ ▷ ψ) 🡒 (φ ▷ (ψ ⋏ □(∼φ)))

/--
  - `W*` in [Vis97]
-/
protected abbrev Wstar := (φ ▷ ψ) 🡒 ((ψ ⋏ □χ) ▷ (ψ ⋏ □χ ⋏ □(∼φ)))

/--
  - `KW1` in [Sve91]
  - `KW1` in [Vis97]
-/
protected abbrev KW1 := (φ ▷ ◇⊤) 🡒 (⊤ ▷ ∼φ)

/--
  - `KW1'` in [Sve91]
-/
protected abbrev KW1' := ((ψ ⋏ φ) ▷ (ψ ⋏ ◇ψ)) 🡒 (ψ ▷ (ψ ⋏ ∼φ))

/--
  - `KW1⁰` in [Sve91]
-/
protected abbrev KW1Zero := ((ψ ⋏ φ) ▷ ◇ψ) 🡒 (ψ ▷ (ψ ⋏ ∼φ))

/--
  - `KW2` in [Vis97]
-/
protected abbrev KW2 := (φ ▷ ◇ψ) 🡒 (ψ ▷ (ψ ⋏ ∼φ))

/--
  - `KW3` in [Vis97]
-/
protected abbrev KW3 := φ ▷ (ψ ⋎ ◇φ) 🡒 φ ▷ ψ

/--
  - `KW4` in [Vis97]
-/
protected abbrev KW4 := φ ▷ ψ 🡒 ψ ▷ (ψ ⋏ □(∼φ))


/--
  Feferman's Principle

  - `F` in [Sve91]
-/
protected abbrev F := (φ ▷ ◇φ) 🡒 □(∼φ)

/--
  - `R` in [G.R11]
-/
protected abbrev R := φ ▷ ψ 🡒 ∼(φ ▷ ∼χ) ▷ (ψ ⋏ □χ)

/--
  - `R*` in [G.R11]
-/
protected abbrev Rstar := φ ▷ ψ 🡒 ∼(φ ▷ ∼χ) ▷ (ψ ⋏ □χ ⋏ □(∼φ))

/--
  - `K13` in [Vis88]: Relative Interpretability Implies Provable Relative Consistency
  - `P_R` in [G.V04]

  Note:
  - `P ⊢ P_R` in [Vis88] Section 16.4
  - `P_R ⊢ W` in [G.V04] Fact 4.1
-/
protected abbrev RIIPRC := φ ▷ ψ 🡒 □(◇φ 🡒 ◇ψ)

end LO.InterpretabilityLogic.Axioms

end
