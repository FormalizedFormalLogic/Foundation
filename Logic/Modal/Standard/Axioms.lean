import Logic.Modal.LogicSymbol

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F] [Box F]
variable (p q r : F)

/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality [Dia F] := ◇p ⟷ ~(□(~p))
abbrev DiaDuality.set [Dia F] : Set F := { Axioms.DiaDuality p | (p) }

protected abbrev K := □(p ⟶ q) ⟶ □p ⟶ □q
abbrev K.set : Set F := { Axioms.K p q | (p) (q) }
notation:max "𝗞" => K.set

protected abbrev T := □p ⟶ p
abbrev T.set : Set F := { Axioms.T p | (p) }
notation:max "𝗧" => T.set

protected abbrev B [Dia F] := p ⟶ □◇p
abbrev B.set [Dia F] : Set F := { Axioms.B p | (p) }
notation:max "𝗕" => B.set

/-- `□`-only version of axiom `𝗕`. -/
protected abbrev B₂ := □p ⟶ □(~□(~p))
abbrev B₂.set : Set F := { Axioms.B₂ p | (p) }
notation:max "𝗕(□)" => B₂.set

protected abbrev D [Dia F] := □p ⟶ ◇p
abbrev D.set [Dia F] : Set F := { Axioms.D p | (p) }
notation:max "𝗗" => D.set


/-- Alternative form of axiom `𝗗`. In sight of provability logic, this can be seen as consistency of theory. -/
protected abbrev D₂ : F := ~(□⊥)
abbrev D₂.set : Set F := { Axioms.D₂ | }
notation:max "𝗗(⊥)" => D₂.set

@[simp] lemma D₂.set.def : 𝗗(⊥) = {(~(□⊥) : F)} := by ext; simp;


protected abbrev Four := □p ⟶ □□p
abbrev Four.set : Set F := { Axioms.Four p | (p) }
notation:max "𝟰" => Four.set

protected abbrev Five [Dia F] := ◇p ⟶ □◇p
abbrev Five.set [Dia F] : Set F := { Axioms.Five p | (p) }
notation:max "𝟱" => Five.set

/-- `□`-only version of axiom `𝟱`. -/
protected abbrev Five₂ := ~□p ⟶ □(~□(~p))
abbrev Five₂.set : Set F := { Axioms.Five₂ p | (p) }
notation:max "𝟱(□)" => Five₂.set

protected abbrev Dot2 [Dia F] := ◇□p ⟶ □◇p
abbrev Dot2.set [Dia F] : Set F := { Axioms.Dot2 p | (p) }
notation:max ".𝟮" => Dot2.set

protected abbrev C4 := □□p ⟶ □p
abbrev C4.set : Set F := { Axioms.C4 p | (p) }
notation:max "𝗖𝟰" => C4.set

protected abbrev CD [Dia F] := ◇p ⟶ □p
abbrev CD.set [Dia F] : Set F := { Axioms.CD p | (p) }
notation:max "𝗖𝗗" => CD.set

protected abbrev Tc := p ⟶ □p
abbrev Tc.set : Set F := { Axioms.Tc p | (p) }
notation:max "𝗧𝗰" => Tc.set

protected abbrev Ver := □p
abbrev Ver.set : Set F := { Axioms.Ver p | (p) }
notation:max "𝗩𝗲𝗿" => Ver.set

protected abbrev Dot3 := □(□p ⟶ q) ⋎ □(□q ⟶ p)
abbrev Dot3.set : Set F := { Axioms.Dot3 p q | (p) (q) }
notation:max ".𝟯" => Dot3.set

protected abbrev Grz := □(□(p ⟶ □p) ⟶ p) ⟶ p
abbrev Grz.set : Set F := { Axioms.Grz p | (p) }
notation:max "𝗚𝗿𝘇" => Grz.set

protected abbrev M [Dia F] := (□◇p ⟶ ◇□p)
abbrev M.set [Dia F] : Set F := { Axioms.M p | (p) }
notation:max "𝗠" => M.set

protected abbrev L := □(□p ⟶ p) ⟶ □p
abbrev L.set : Set F := { Axioms.L p | (p) }
notation:max "𝗟" => L.set

protected abbrev H := □(□p ⟷ p) ⟶ □p
abbrev H.set : Set F := { Axioms.H p | (p) }
notation:max "𝗛" => H.set

protected abbrev Dz := Axioms.T (□p ⋎ □q)
abbrev Dz.set : Set F := { Axioms.Dz p q | (p) (q) }
notation:max "𝗗𝘇" => Dz.set

end LO.Axioms
