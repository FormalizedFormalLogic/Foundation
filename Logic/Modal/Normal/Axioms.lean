import Logic.Modal.Normal.Formula

@[simp]
lemma _root_.Set.subset_triunion₁ (s₁ s₂ s₃ : Set F) : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_left _ _) (Set.subset_union_left _ _)

@[simp]
lemma _root_.Set.subset_triunion₂  (s₁ s₂ s₃ : Set F) : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_right _ _) (Set.subset_union_left _ _)

@[simp]
lemma _root_.Set.subset_triunion₃ (s₁ s₂ s₃ : Set F) : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.subset_union_right _ _

namespace LO.Modal.Normal

section Axioms

variable {F : Type u} [ModalLogicSymbol F] (p q : F)

/-- a.k.a. Distribution Axiom -/
def AxiomK := □(p ⟶ q) ⟶ □p ⟶ □q

def AxiomT := □p ⟶ p

def AxiomB := p ⟶ □◇p

def AxiomD := □p ⟶ ◇p

def Axiom4 := □p ⟶ □□p

def Axiom5 := ◇p ⟶ □◇p

def AxiomDot2 := ◇□p ⟶ □◇p

def AxiomDot3 := □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

def AxiomGrz := □(□(p ⟶ □p) ⟶ p) ⟶ p

def AxiomM := (□◇p ⟶ ◇□p)

def AxiomCD := ◇p ⟶ □p

def AxiomC4 := □□p ⟶ □p

def AxiomL := □(□p ⟶ p) ⟶ □p

end Axioms

abbrev AxiomSet (α) := Set (Formula α)

section AxiomSet

variable {p q : Formula α}

def AxiomK.set : AxiomSet α := { AxiomK p q | (p) (q) }
notation "𝐊" => AxiomK.set
@[simp] lemma AxiomK.set.include : (AxiomK p q) ∈ 𝐊 := by simp [set, AxiomK];

def AxiomT.set : AxiomSet α := { AxiomT p | p }
notation "𝐓" => AxiomT.set
@[simp] lemma AxiomT.set.include : (AxiomT p) ∈ 𝐓 := by simp [set];

def AxiomB.set : AxiomSet α := { AxiomB p | p }
notation "𝐁" => AxiomB.set
@[simp] lemma AxiomB.set.include : (AxiomB p) ∈ 𝐁 := by simp [set];

def AxiomD.set : AxiomSet α := { AxiomD p | p }
notation "𝐃" => AxiomD.set
@[simp] lemma AxiomD.set.include : (AxiomD p) ∈ 𝐃 := by simp [set];

def Axiom4.set : AxiomSet α := { Axiom4 p | p }
notation "𝟒" => Axiom4.set
@[simp] lemma Axiom4.set.include : (Axiom4 p) ∈ 𝟒 := by simp [set];

def Axiom5.set : AxiomSet α := { Axiom5 p | p }
notation "𝟓" => Axiom5.set
@[simp] lemma Axiom5.set.include : (Axiom5 p) ∈ 𝟓 := by simp [set];

def AxiomL.set : AxiomSet α := { AxiomL p | p }
notation "𝐋" => AxiomL.set
@[simp] lemma AxiomL.set.include : (AxiomL p) ∈ 𝐋 := by simp [set];

def AxiomDot2.set : AxiomSet α := { AxiomDot2 p | p }
notation ".𝟐" => AxiomDot2.set
@[simp] lemma AxiomDot2.set.include : (AxiomDot2 p) ∈ .𝟐 := by simp [set];

def AxiomDot3.set : AxiomSet α := { AxiomDot3 p q | (p) (q) }
notation ".𝟑" => AxiomDot3.set
@[simp] lemma AxiomDot3.set.include : (AxiomDot3 p q) ∈ .𝟑 := by simp [set]; aesop;

def AxiomGrz.set : AxiomSet α := { AxiomGrz p | p }
notation "𝐆𝐫𝐳" => AxiomGrz.set
@[simp] lemma AxiomGrz.set.include : (AxiomGrz p) ∈ 𝐆𝐫𝐳 := by simp [set];

def AxiomM.set : AxiomSet α := { AxiomM p | p }
notation "𝐌" => AxiomM.set
@[simp] lemma AxiomM.set.include : (AxiomM p) ∈ 𝐌 := by simp [set];

def AxiomCD.set : AxiomSet α := { AxiomCD p | p }
notation "𝐂𝐃" => AxiomCD.set
@[simp] lemma AxiomCD.set.include : (AxiomCD p) ∈ 𝐂𝐃 := by simp [set];

def AxiomC4.set : AxiomSet α := { AxiomC4 p | p }
notation "𝐂𝟒" => AxiomC4.set
@[simp] lemma AxiomC4.set.include : (AxiomC4 p) ∈ 𝐂𝟒 := by simp [set];

end AxiomSet

section Logics

@[simp] abbrev LogicK : AxiomSet α := AxiomK.set

namespace LogicK

@[simp] lemma subset_K : 𝐊 ⊆ (𝐊 : AxiomSet α) := by apply Set.Subset.refl

end LogicK

def LogicKD : AxiomSet α := 𝐊 ∪ 𝐃
notation "𝐊𝐃" => LogicKD

def LogicKT4 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒
@[simp] abbrev LogicS4 : AxiomSet α := LogicKT4
notation "𝐒𝟒" => LogicS4

namespace LogicS4

@[simp] lemma include_AxiomK : AxiomK p q ∈ 𝐒𝟒 := by simp [LogicKT4]
@[simp] lemma include_AxiomT : AxiomT p ∈ 𝐒𝟒 := by simp [LogicKT4]
@[simp] lemma include_Axiom4 : Axiom4 p ∈ 𝐒𝟒 := by simp [LogicKT4]
@[simp] lemma subset_K : 𝐊 ⊆ (𝐒𝟒 : AxiomSet α) := by apply Set.subset_triunion₁
@[simp] lemma subset_T : 𝐓 ⊆ (𝐒𝟒 : AxiomSet α) := by apply Set.subset_triunion₂
@[simp] lemma subset_4 : 𝟒 ⊆ (𝐒𝟒 : AxiomSet α) := by apply Set.subset_triunion₃

end LogicS4


def LogicS4Dot2 : AxiomSet α := 𝐒𝟒 ∪ .𝟐
notation "𝐒𝟒.𝟐" => LogicS4Dot2

namespace LogicS4Dot2

@[simp] lemma include_AxiomDot2 : AxiomDot2 p ∈ 𝐒𝟒.𝟐 := by simp [LogicS4Dot2]
@[simp] lemma subset_S4 : 𝐒𝟒 ⊆ (𝐒𝟒.𝟐 : AxiomSet α) := by simp [LogicKT4, LogicS4Dot2]
@[simp] lemma subset_Dot2 : AxiomDot2.set ⊆ (𝐒𝟒.𝟐 : AxiomSet α) := by simp [LogicS4Dot2]

end LogicS4Dot2

def LogicS4Dot3 : AxiomSet α := 𝐒𝟒 ∪ .𝟑
notation "𝐒𝟒.𝟑" => LogicS4Dot3

namespace LogicS4Dot3

@[simp] lemma include_AxiomDot3 : AxiomDot3 p q ∈ 𝐒𝟒.𝟑 := by simp [LogicS4Dot3, AxiomDot3.set]; aesop;
@[simp] lemma subset_S4 : 𝐒𝟒 ⊆ (𝐒𝟒.𝟑 : AxiomSet α) := by simp [LogicS4Dot3]
@[simp] lemma subset_Dot3 : AxiomDot3.set ⊆ (𝐒𝟒.𝟑 : AxiomSet α) := by simp [LogicS4Dot3]

end LogicS4Dot3


def LogicS4Grz : AxiomSet α := 𝐒𝟒 ∪ 𝐆𝐫𝐳
notation "𝐒𝟒𝐆𝐫𝐳" => LogicS4Grz

namespace LogicS4Grz

@[simp] lemma include_AxiomGrz : AxiomGrz p ∈ 𝐒𝟒𝐆𝐫𝐳 := by simp [LogicS4Grz]
@[simp] lemma subset_Dot2 : AxiomGrz.set ⊆ (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α) := by simp [LogicS4Grz]
@[simp] lemma subset_LogicS4_set : 𝐒𝟒 ⊆ (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α) := by simp [LogicS4Grz]

end LogicS4Grz


def LogicKT5 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟓
@[simp] abbrev LogicS5 {F} := @LogicKT5 F
notation "𝐒𝟓" => LogicS5

namespace LogicS5

@[simp] lemma include_AxiomK : AxiomK p q ∈ 𝐒𝟓 := by simp [LogicKT5]
@[simp] lemma include_AxiomT : AxiomT p ∈ 𝐒𝟓 := by simp [LogicKT5]
@[simp] lemma include_Axiom5 : Axiom5 p ∈ 𝐒𝟓 := by simp [LogicKT5]
@[simp] lemma subset_K : 𝐊 ⊆ (𝐒𝟓 : AxiomSet α) := by apply Set.subset_triunion₁
@[simp] lemma subset_T : 𝐓 ⊆ (𝐒𝟓 : AxiomSet α) := by apply Set.subset_triunion₂
@[simp] lemma subset_5 : 𝟓 ⊆ (𝐒𝟓 : AxiomSet α) := by apply Set.subset_triunion₃

end LogicS5


def LogicGL : AxiomSet α := 𝐊 ∪ 𝐋
notation "𝐆𝐋" => LogicGL

namespace LogicGL

@[simp] lemma include_AxiomK : AxiomK p q ∈ 𝐆𝐋 := by simp [LogicGL]
@[simp] lemma include_AxiomL : AxiomL p ∈ 𝐆𝐋 := by simp [LogicGL]
@[simp] lemma subset_K : 𝐊 ⊆ (𝐆𝐋 : AxiomSet α) := by simp [LogicGL, LogicK]
@[simp] lemma subset_L : 𝐋 ⊆ (𝐆𝐋 : AxiomSet α) := by simp [LogicGL]

end LogicGL

end Logics

end LO.Modal.Normal
