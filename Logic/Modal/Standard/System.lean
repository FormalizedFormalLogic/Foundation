import Logic.Logic.System
import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Context
import Logic.Modal.LogicSymbol

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [System F S]
variable (𝓢 : S)

namespace Axioms

variable (p q : F)

protected abbrev K := □(p ⟶ q) ⟶ □p ⟶ □q

protected abbrev T := □p ⟶ p

protected abbrev B := p ⟶ □◇p

protected abbrev D := □p ⟶ ◇p

protected abbrev Four := □p ⟶ □□p

protected abbrev Five := ◇p ⟶ □◇p

protected abbrev Dot2 := ◇□p ⟶ □◇p

protected abbrev C4 := □□p ⟶ □p

protected abbrev CD := ◇p ⟶ □p

protected abbrev Tc := p ⟶ □p

protected abbrev Ver := □p

protected abbrev Dot3 := □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

protected abbrev Grz := □(□(p ⟶ □p) ⟶ p) ⟶ p

protected abbrev M := (□◇p ⟶ ◇□p)

protected abbrev L := □(□p ⟶ p) ⟶ □p

end Axioms


class Necessitation where
  nec {p : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

class HasAxiomK where
  K (p q : F) : 𝓢 ⊢ Axioms.K p q

class HasAxiomT where
  T (p : F) : 𝓢 ⊢ Axioms.T p

class HasAxiomD where
  D (p : F) : 𝓢 ⊢ Axioms.D p

class HasAxiomB where
  B (p : F) : 𝓢 ⊢ Axioms.B p

class HasAxiomFour where
  Four (p : F) : 𝓢 ⊢ Axioms.Four p

class HasAxiomFive where
  Five (p : F) : 𝓢 ⊢ Axioms.Five p

class HasAxiomL where
  L (p : F) : 𝓢 ⊢ Axioms.L p

class HasAxiomDot2 where
  Dot2 (p : F) : 𝓢 ⊢ Axioms.Dot2 p

class HasAxiomDot3 where
  Dot3 (p q : F) : 𝓢 ⊢ Axioms.Dot3 p q

class HasAxiomGrz where
  Grz (p : F) : 𝓢 ⊢ Axioms.Grz p

class HasAxiomTc where
  Tc (p : F) : 𝓢 ⊢ Axioms.Tc p

class HasAxiomVer where
  Ver (p : F) : 𝓢 ⊢ Axioms.Ver p

class K extends Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢

class KT extends K 𝓢, HasAxiomT 𝓢

class KD extends K 𝓢, HasAxiomD 𝓢

class K4 extends K 𝓢, HasAxiomFour 𝓢

class S4 extends K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢

class S5 extends K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢

class S4Dot2 extends S4 𝓢, HasAxiomDot2 𝓢

class S4Dot3 extends S4 𝓢, HasAxiomDot3 𝓢

class S4Grz extends S4 𝓢, HasAxiomGrz 𝓢

class GL extends K 𝓢, HasAxiomL 𝓢

class Triv extends K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢

class Ver extends K 𝓢, HasAxiomVer 𝓢

end LO.System
