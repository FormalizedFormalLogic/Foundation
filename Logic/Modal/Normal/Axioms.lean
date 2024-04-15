import Logic.Modal.Normal.Formula

section

namespace Set

variable (s₁ s₂ s₃ s₄ : Set F)

@[simp] lemma subset_triunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_triunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans (Set.subset_union_right _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_triunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := by simp only [Set.subset_union_right]

@[simp] lemma subset_tetraunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    (Set.subset_union_left _ _)
    $ Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp]
lemma subset_tetraunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    (Set.subset_union_right _ _)
    $ Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp] lemma subset_tetraunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp_all
@[simp] lemma subset_tetraunion₄ : s₄ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp_all

end Set

end

namespace LO.Modal.Normal

section Axioms

variable {F : Type u} [ModalLogicSymbol F] (p q : F)

/-- a.k.a. Distribution Axiom -/
abbrev axiomK := □(p ⟶ q) ⟶ □p ⟶ □q

abbrev axiomT := □p ⟶ p

abbrev axiomB := p ⟶ □◇p

abbrev axiomD := □p ⟶ ◇p

abbrev axiomFour := □p ⟶ □□p

abbrev axiomFive := ◇p ⟶ □◇p

abbrev axiomDot2 := ◇□p ⟶ □◇p

abbrev axiomC4 := □□p ⟶ □p

abbrev axiomCD := ◇p ⟶ □p

abbrev axiomTc := p ⟶ □p

abbrev axiomVer := □p

abbrev axiomDot3 := □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

abbrev axiomGrz := □(□(p ⟶ □p) ⟶ p) ⟶ p

abbrev axiomM := (□◇p ⟶ ◇□p)

abbrev axiomL := □(□p ⟶ p) ⟶ □p

end Axioms

abbrev AxiomSet (α) := Set (Formula α)

section AxiomSet

variable {p q : Formula α}

abbrev AxiomSet.K : AxiomSet α := { axiomK p q | (p) (q) }
notation "𝐊" => AxiomSet.K

abbrev AxiomSet.T : AxiomSet α := { axiomT p | p }
notation "𝐓" => AxiomSet.T

abbrev AxiomSet.B : AxiomSet α := { axiomB p | p }
notation "𝐁" => AxiomSet.B

abbrev AxiomSet.D : AxiomSet α := { axiomD p | p }
notation "𝐃" => AxiomSet.D

abbrev AxiomSet.Four : AxiomSet α := { axiomFour p | p }
notation "𝟒" => AxiomSet.Four

abbrev AxiomSet.Five : AxiomSet α := { axiomFive p | p }
notation "𝟓" => AxiomSet.Five

abbrev AxiomSet.L : AxiomSet α := { axiomL p | p }
notation "𝐋" => AxiomSet.L

abbrev AxiomSet.Dot2 : AxiomSet α := { axiomDot2 p | p }
notation ".𝟐" => AxiomSet.Dot2

abbrev AxiomSet.Dot3 : AxiomSet α := { axiomDot3 p q | (p) (q) }
notation ".𝟑" => AxiomSet.Dot3

abbrev AxiomSet.Grz : AxiomSet α := { axiomGrz p | p }
notation "𝐆𝐫𝐳" => AxiomSet.Grz

abbrev AxiomSet.M : AxiomSet α := { axiomM p | p }
notation "𝐌" => AxiomSet.M

abbrev AxiomSet.CD : AxiomSet α := { axiomCD p | p }
notation "𝐂𝐃" => AxiomSet.CD

abbrev AxiomSet.C4 : AxiomSet α := { axiomC4 p | p }
notation "𝐂𝟒" => AxiomSet.C4

end AxiomSet

section Logics

abbrev AxiomSet.KT : AxiomSet α := 𝐊 ∪ 𝐓
notation "𝐊𝐓" => AxiomSet.KT

abbrev AxiomSet.KD : AxiomSet α := 𝐊 ∪ 𝐃
notation "𝐊𝐃" => AxiomSet.KD

abbrev AxiomSet.K4 : AxiomSet α := 𝐊 ∪ 𝟒
notation "𝐊𝟒" => AxiomSet.K4

abbrev AxiomSet.KT4 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒
abbrev AxiomSet.S4 : AxiomSet α := AxiomSet.KT4
notation "𝐒𝟒" => AxiomSet.S4

abbrev AxiomSet.S4Dot2 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ .𝟐
notation "𝐒𝟒.𝟐" => AxiomSet.S4Dot2

abbrev AxiomSet.S4Dot3 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ .𝟑
notation "𝐒𝟒.𝟑" => AxiomSet.S4Dot3

abbrev AxiomSet.S4Grz : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ 𝐆𝐫𝐳
notation "𝐒𝟒𝐆𝐫𝐳" => AxiomSet.S4Grz

abbrev AxiomSet.KT5 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟓
abbrev AxiomSet.S5 : AxiomSet α := AxiomSet.KT5
notation "𝐒𝟓" => AxiomSet.S5

abbrev AxiomSet.KT4B : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ 𝐁
notation "𝐊𝐓𝟒𝐁" => AxiomSet.KT4B

abbrev AxiomSet.GL : AxiomSet α := 𝐊 ∪ 𝐋
notation "𝐆𝐋" => AxiomSet.GL

end Logics

end LO.Modal.Normal
