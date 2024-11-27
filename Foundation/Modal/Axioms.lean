import Foundation.Modal.LogicSymbol
import Foundation.Vorspiel.Geach

namespace LO.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)


section Basic

/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality [Dia F] := ◇φ ⭤ ∼(□(∼φ))
abbrev DiaDuality.set [Dia F] : Set F := { Axioms.DiaDuality φ | (φ) }

protected abbrev K := □(φ ➝ ψ) ➝ □φ ➝ □ψ
abbrev K.set : Set F := { Axioms.K φ ψ | (φ) (ψ) }
notation:max "𝗞" => K.set

protected abbrev T := □φ ➝ φ
abbrev T.set : Set F := { Axioms.T φ | (φ) }
notation:max "𝗧" => T.set

protected abbrev B [Dia F] := φ ➝ □◇φ
abbrev B.set [Dia F] : Set F := { Axioms.B φ | (φ) }
notation:max "𝗕" => B.set

/-- `□`-only version of axiom `𝗕`. -/
protected abbrev B₂ := □φ ➝ □(∼□(∼φ))
abbrev B₂.set : Set F := { Axioms.B₂ φ | (φ) }
notation:max "𝗕(□)" => B₂.set

protected abbrev D [Dia F] := □φ ➝ ◇φ
abbrev D.set [Dia F] : Set F := { Axioms.D φ | (φ) }
notation:max "𝗗" => D.set


protected abbrev P : F := ∼(□⊥)
abbrev P.set : Set F := { Axioms.P | }
notation:max "𝗣" => P.set
@[simp] lemma P.set.def : 𝗣 = {(∼(□⊥) : F)} := by ext; simp;


protected abbrev Four := □φ ➝ □□φ
abbrev Four.set : Set F := { Axioms.Four φ | (φ) }
notation:max "𝟰" => Four.set

protected abbrev Five [Dia F] := ◇φ ➝ □◇φ
abbrev Five.set [Dia F] : Set F := { Axioms.Five φ | (φ) }
notation:max "𝟱" => Five.set

/-- `□`-only version of axiom `𝟱`. -/
protected abbrev Five₂ := ∼□φ ➝ □(∼□(∼φ))
abbrev Five₂.set : Set F := { Axioms.Five₂ φ | (φ) }
notation:max "𝟱(□)" => Five₂.set

protected abbrev Dot2 [Dia F] := ◇□φ ➝ □◇φ
abbrev Dot2.set [Dia F] : Set F := { Axioms.Dot2 φ | (φ) }
notation:max ".𝟮" => Dot2.set

protected abbrev C4 := □□φ ➝ □φ
abbrev C4.set : Set F := { Axioms.C4 φ | (φ) }
notation:max "𝗖𝟰" => C4.set

protected abbrev CD [Dia F] := ◇φ ➝ □φ
abbrev CD.set [Dia F] : Set F := { Axioms.CD φ | (φ) }
notation:max "𝗖𝗗" => CD.set

protected abbrev Tc := φ ➝ □φ
abbrev Tc.set : Set F := { Axioms.Tc φ | (φ) }
notation:max "𝗧𝗰" => Tc.set

protected abbrev Ver := □φ
abbrev Ver.set : Set F := { Axioms.Ver φ | (φ) }
notation:max "𝗩𝗲𝗿" => Ver.set

protected abbrev Dot3 := □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ)
abbrev Dot3.set : Set F := { Axioms.Dot3 φ ψ | (φ) (ψ) }
notation:max ".𝟯" => Dot3.set

protected abbrev Grz := □(□(φ ➝ □φ) ➝ φ) ➝ φ
abbrev Grz.set : Set F := { Axioms.Grz φ | (φ) }
notation:max "𝗚𝗿𝘇" => Grz.set

protected abbrev M [Dia F] := (□◇φ ➝ ◇□φ)
abbrev M.set [Dia F] : Set F := { Axioms.M φ | (φ) }
notation:max "𝗠" => M.set

protected abbrev L := □(□φ ➝ φ) ➝ □φ
abbrev L.set : Set F := { Axioms.L φ | (φ) }
notation:max "𝗟" => L.set

protected abbrev H := □(□φ ⭤ φ) ➝ □φ
abbrev H.set : Set F := { Axioms.H φ | (φ) }
notation:max "𝗛" => H.set

end Basic


section Geach

protected abbrev Geach (t : GeachConfluent.Taple) (φ : F) := ◇^[t.i](□^[t.m]φ) ➝ □^[t.j](◇^[t.n]φ)
abbrev Geach.set (t : GeachConfluent.Taple) : Set F := { Axioms.Geach t φ | (φ) }
notation:max "𝗴𝗲(" t ")" => Geach.set t


section

lemma T.is_geach : (𝗧 : Set F) = 𝗴𝗲(⟨0, 0, 1, 0⟩) := rfl

lemma B.is_geach : (𝗕 : Set F) = 𝗴𝗲(⟨0, 1, 0, 1⟩) := rfl

lemma D.is_geach : (𝗗 : Set F) = 𝗴𝗲(⟨0, 0, 1, 1⟩) := rfl

lemma Four.is_geach : (𝟰 : Set F) = 𝗴𝗲(⟨0, 2, 1, 0⟩) := rfl

lemma Five.is_geach : (𝟱 : Set F) = 𝗴𝗲(⟨1, 1, 0, 1⟩) := rfl

lemma Dot2.is_geach : (.𝟮 : Set F) = 𝗴𝗲(⟨1, 1, 1, 1⟩) := rfl

lemma C4.is_geach : (𝗖𝟰 : Set F) = 𝗴𝗲(⟨0, 1, 2, 0⟩) := rfl

lemma CD.is_geach : (𝗖𝗗 : Set F) = 𝗴𝗲(⟨1, 1, 0, 0⟩) := rfl

lemma Tc.is_geach : (𝗧𝗰 : Set F) = 𝗴𝗲(⟨0, 1, 0, 0⟩) := rfl

end


def MultiGeach.set : List (GeachConfluent.Taple) → Set F
  | [] => ∅
  | t :: ts => 𝗴𝗲(t) ∪ (MultiGeach.set ts)
notation:max "𝗚𝗲(" ts ")" => MultiGeach.set ts

namespace MultiGeach

@[simp] lemma def_nil : 𝗚𝗲([]) = (∅ : Set F) := by simp [MultiGeach.set]

lemma def_one {t : GeachConfluent.Taple} : (𝗚𝗲([t]) : Set F) = 𝗴𝗲(t) := by simp [MultiGeach.set]

lemma def_two {t₁ t₂ : GeachConfluent.Taple} : (𝗚𝗲([t₁, t₂]) : Set F) = 𝗴𝗲(t₁) ∪ 𝗴𝗲(t₂) := by simp [MultiGeach.set]

lemma def_three {t₁ t₂ t₃ : GeachConfluent.Taple} : (𝗚𝗲([t₁, t₂, t₃]) : Set F) = 𝗴𝗲(t₁) ∪ 𝗴𝗲(t₂) ∪ 𝗴𝗲(t₃) := by simp [MultiGeach.set, Set.union_assoc];

@[simp] lemma iff_cons : 𝗚𝗲(x :: l) = (𝗴𝗲(x) : Set F) ∪ 𝗚𝗲(l) := by simp only [MultiGeach.set];

lemma mem (h : x ∈ l) : (𝗴𝗲(x) : Set F) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => contradiction;
  | cons a as ih =>
    simp_all;
    cases h;
    . subst_vars; tauto;
    . apply Set.subset_union_of_subset_right $ ih (by assumption);

end MultiGeach

end Geach

end LO.Axioms
