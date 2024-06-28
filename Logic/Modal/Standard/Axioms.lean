import Logic.Modal.LogicSymbol

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F]
variable (p q r : F)

protected abbrev K := □(p ⟶ q) ⟶ □p ⟶ □q
abbrev K.set : Set F := { Axioms.K p q | (p) (q) }
notation "𝗞" => K.set

protected abbrev T := □p ⟶ p
abbrev T.set : Set F := { Axioms.T p | (p) }
notation "𝗧" => T.set

protected abbrev B := p ⟶ □◇p
abbrev B.set : Set F := { Axioms.B p | (p) }
notation "𝗕" => B.set

protected abbrev D := □p ⟶ ◇p
abbrev D.set : Set F := { Axioms.D p | (p) }
notation "𝗗" => D.set

protected abbrev Four := □p ⟶ □□p
abbrev Four.set : Set F := { Axioms.Four p | (p) }
notation "𝟰" => Four.set

protected abbrev Five := ◇p ⟶ □◇p
abbrev Five.set : Set F := { Axioms.Five p | (p) }
notation "𝟱" => Five.set

protected abbrev Dot2 := ◇□p ⟶ □◇p
abbrev Dot2.set : Set F := { Axioms.Dot2 p | (p) }
notation ".𝟮" => Dot2.set

protected abbrev C4 := □□p ⟶ □p
abbrev C4.set : Set F := { Axioms.C4 p | (p) }
notation "𝗖𝟰" => C4.set

protected abbrev CD := ◇p ⟶ □p
abbrev CD.set : Set F := { Axioms.CD p | (p) }
notation "𝗖𝗗" => CD.set

protected abbrev Tc := p ⟶ □p
abbrev Tc.set : Set F := { Axioms.Tc p | (p) }
notation "𝗧𝗰" => Tc.set

protected abbrev Ver := □p
abbrev Ver.set : Set F := { Axioms.Ver p | (p) }
notation "𝗩𝗲𝗿" => Ver.set

protected abbrev Dot3 := □(□p ⟶ q) ⋎ □(□q ⟶ p)
abbrev Dot3.set : Set F := { Axioms.Dot3 p q | (p) (q) }
notation ".𝟯" => Dot3.set

protected abbrev Grz := □(□(p ⟶ □p) ⟶ p) ⟶ p
abbrev Grz.set : Set F := { Axioms.Grz p | (p) }
notation "𝗚𝗿𝘇" => Grz.set

protected abbrev M := (□◇p ⟶ ◇□p)
abbrev M.set : Set F := { Axioms.M p | (p) }
notation "𝗠" => M.set

protected abbrev L := □(□p ⟶ p) ⟶ □p
abbrev L.set : Set F := { Axioms.L p | (p) }
notation "𝗟" => L.set

protected abbrev H := □(□p ⟷ p) ⟶ □p
abbrev H.set : Set F := { Axioms.H p | (p) }
notation "𝗛" => H.set

end LO.Axioms
