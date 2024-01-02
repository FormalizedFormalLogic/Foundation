import Logic.Modal.Basic.Formula

lemma _root_.Set.subset_triunion₁ (s₁ s₂ s₃ : Set F) : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_left _ _) (Set.subset_union_left _ _)

lemma _root_.Set.subset_triunion₂  (s₁ s₂ s₃ : Set F) : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_right _ _) (Set.subset_union_left _ _)

lemma _root_.Set.subset_triunion₃ (s₁ s₂ s₃ : Set F) : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.subset_union_right _ _

namespace LO.Modal

variable {F : Type u} [ModalLogicSymbol F]

section Axioms

variable (p q : F)

@[simp] abbrev AxiomK := □(p ⟶ q) ⟶ □p ⟶ □q
def AxiomK.ctx : Set F := { AxiomK p q | (p) (q) }
notation "𝐊" => AxiomK.ctx
@[simp] lemma AxiomK.ctx.includes_AxiomK : (AxiomK p q) ∈ 𝐊 := by simp [ctx]; aesop;

@[simp] abbrev AxiomT := □p ⟶ p
def AxiomT.ctx : Set F := { AxiomT p | p }
notation "𝐓" => AxiomT.ctx
@[simp] lemma AxiomT.ctx.includes_AxiomT : (AxiomT p) ∈ 𝐓 := by simp [ctx];

@[simp] abbrev AxiomB := p ⟶ □◇p
def AxiomB.ctx : Set F := { AxiomB p | p }
notation "𝐁" => AxiomB.ctx
@[simp] lemma AxiomB.ctx.includes_AxiomB : (AxiomB p) ∈ 𝐁 := by simp [ctx];

@[simp] abbrev AxiomD := □p ⟶ ◇p
def AxiomD.ctx : Set F := { AxiomD p | p }
notation "𝐃" => AxiomD.ctx
@[simp] lemma AxiomD.ctx.includes_AxiomD : (AxiomD p) ∈ 𝐃 := by simp [ctx];

@[simp] abbrev Axiom4 := □p ⟶ □□p
def Axiom4.ctx : Set F := { Axiom4 p | p }
notation "𝟒" => Axiom4.ctx
@[simp] lemma Axiom4.ctx.includes_Axiom4 : (Axiom4 p) ∈ 𝟒 := by simp [ctx];

@[simp] abbrev Axiom5 := ◇p ⟶ □◇p
def Axiom5.ctx : Set F := { Axiom5 p | p }
notation "𝟓" => Axiom5.ctx
@[simp] lemma Axiom5.ctx.includes_Axiom5 : (Axiom5 p) ∈ 𝟓 := by simp [ctx];

@[simp] abbrev AxiomL := □(□p ⟶ p) ⟶ □p
def AxiomL.ctx : Set F := { AxiomL p | p }
notation "𝐋" => AxiomL.ctx
@[simp] lemma AxiomL.ctx.includes_AxiomL : (AxiomL p) ∈ 𝐋 := by simp [ctx];

@[simp] abbrev AxiomDot2 := ◇□p ⟶ □◇p
def AxiomDot2.ctx : Set F := { AxiomDot2 p | p }
notation ".𝟐" => AxiomDot2.ctx
@[simp] lemma AxiomDot2.ctx.includes_AxiomDot2 : (AxiomDot2 p) ∈ .𝟐 := by simp [ctx];

@[simp] abbrev AxiomDot3 := □(□p ⟶ □q) ⋎ □(□q ⟶ □p)
def AxiomDot3.ctx : Set F := { AxiomDot3 p q | (p) (q) }
notation ".𝟑" => AxiomDot3.ctx
@[simp] lemma AxiomDot3.ctx.includes_AxiomDot3 : (AxiomDot3 p q) ∈ .𝟑 := by simp [ctx]; aesop;

@[simp] abbrev AxiomGrz := □(□(p ⟶ □p) ⟶ p) ⟶ p
def AxiomGrz.ctx : Set F := { AxiomGrz p | p }
notation "𝐆𝐫𝐳" => AxiomGrz.ctx
@[simp] lemma AxiomGrz.ctx.includes_AxiomGrz : (AxiomGrz p) ∈ 𝐆𝐫𝐳 := by simp [ctx];

@[simp] abbrev AxiomM := (□◇p ⟶ ◇□p)
def AxiomM.ctx : Set F := { AxiomM p | p }
notation "𝐌" => AxiomM.ctx
@[simp] lemma AxiomM.ctx.includes_AxiomM : (AxiomM p) ∈ 𝐌 := by simp [ctx];

@[simp] abbrev AxiomCD := ◇p ⟶ □p
def AxiomCD.ctx : Set F := { AxiomCD p | p }
notation "𝐂𝐃" => AxiomCD.ctx
@[simp] lemma AxiomCD.ctx.includes_AxiomCD : (AxiomCD p) ∈ 𝐂𝐃 := by simp [ctx];

@[simp] abbrev AxiomC4 := □□p ⟶ □p
def AxiomC4.ctx : Set F := { AxiomC4 p | p }
notation "𝐂𝟒" => AxiomC4.ctx
@[simp] lemma AxiomC4.ctx.includesAxiomC4 : (AxiomC4 p) ∈ 𝐂𝟒 := by simp [ctx];

end Axioms


section Logics

abbrev LogicK.ctx : Set F := 𝐊

abbrev LogicKD.ctx : Set F := 𝐊 ∪ 𝐃
abbrev LogicKD4.ctx : Set F := 𝐊 ∪ 𝐃 ∪ 𝟒
abbrev LogicKD5.ctx : Set F := 𝐊 ∪ 𝐃 ∪ 𝟓
abbrev LogicKDB.ctx : Set F := 𝐊 ∪ 𝐃 ∪ 𝐁
abbrev LogicKD45.ctx : Set F := 𝐊 ∪ 𝐃 ∪ 𝟒 ∪ 𝟓

abbrev LogicKT.ctx : Set F := 𝐊 ∪ 𝐓
abbrev LogicKTB.ctx : Set F := 𝐊 ∪ 𝐓 ∪ 𝐁
abbrev LogicKT4.ctx : Set F := 𝐊 ∪ 𝐓 ∪ 𝟒
abbrev LogicKT5.ctx : Set F := 𝐊 ∪ 𝐓 ∪ 𝟓

abbrev LogicKB.ctx : Set F := 𝐊 ∪ 𝐁
abbrev LogicKB5.ctx : Set F := 𝐊 ∪ 𝐁 ∪ 𝟓

abbrev LogicK4.ctx : Set F := 𝐊 ∪ 𝟒
abbrev LogicK45.ctx : Set F := 𝐊 ∪ 𝟒 ∪ 𝟓

abbrev LogicK5.ctx : Set F := 𝐊 ∪ 𝟓

/-- equals to `𝐊 ∪ 𝐓 ∪ 𝟒`  -/
abbrev LogicS4.ctx : Set F := LogicKT4.ctx
notation "𝐒𝟒" => LogicS4.ctx

@[simp] lemma LogicS4.ctx.subsets_K : 𝐊 ⊆ (𝐒𝟒 : Set F) := by apply Set.subset_triunion₁
@[simp] lemma LogicS4.ctx.subsets_T : 𝐓 ⊆ (𝐒𝟒 : Set F) := by apply Set.subset_triunion₂
@[simp] lemma LogicS4.ctx.subsets_4 : 𝟒 ⊆ (𝐒𝟒 : Set F) := by apply Set.subset_triunion₃

/-- equals to `𝐊 ∪ 𝐓 ∪ 𝟓` -/
abbrev LogicS5.ctx : Set F := LogicKT5.ctx
notation "𝐒𝟓" => LogicS5.ctx

@[simp] lemma LogicS5.ctx.subsets_K : 𝐊 ⊆ (𝐒𝟓 : Set F) := by apply Set.subset_triunion₁
@[simp] lemma LogicS5.ctx.subsets_T : 𝐓 ⊆ (𝐒𝟓 : Set F) := by apply Set.subset_triunion₂
@[simp] lemma LogicS5.ctx.subsets_5 : 𝟓 ⊆ (𝐒𝟓 : Set F) := by apply Set.subset_triunion₃

abbrev LogicGL.ctx : Set F := 𝐊 ∪ 𝐋
notation "𝐆𝐋" => LogicGL.ctx

@[simp] lemma LogicGL.ctx.subsets_K : 𝐊 ⊆ (𝐆𝐋 : Set F) := by aesop;
@[simp] lemma LogicGL.ctx.subsets_L : 𝐋 ⊆ (𝐆𝐋 : Set F) := by aesop;

abbrev LogicS4Dot2.ctx : Set F := 𝐒𝟒 ∪ .𝟐
notation "𝐒𝟒.𝟐" => LogicS4Dot2.ctx

@[simp] lemma LogicS4Dot2.ctx.subsets_S4 : 𝐒𝟒 ⊆ (𝐒𝟒.𝟐 : Set F) := by aesop;
@[simp] lemma LogicS4Dot2.ctx.subsets_Dot2 : .𝟐 ⊆ (𝐒𝟒.𝟐 : Set F) := by aesop;

abbrev LogicS4Dot3.ctx : Set F := 𝐒𝟒 ∪ .𝟑
notation "𝐒𝟒.𝟑" => LogicS4Dot3.ctx

@[simp] lemma LogicS4Dot3.ctx.subsets_S4 : 𝐒𝟒 ⊆ (𝐒𝟒.𝟑 : Set F) := by aesop;
@[simp] lemma LogicS4Dot3.ctx.subsets_Dot3 : .𝟑 ⊆ (𝐒𝟒.𝟑 : Set F) := by aesop;

abbrev LogicS4Grz.ctx : Set F := 𝐒𝟒 ∪ 𝐆𝐫𝐳
notation "𝐒𝟒𝐆𝐫𝐳" => LogicS4Grz.ctx

@[simp] lemma LogicS4Grz.ctx.subsets_S4 : 𝐒𝟒 ⊆ (𝐒𝟒𝐆𝐫𝐳 : Set F) := by aesop;
@[simp] lemma LogicS4Grz.ctx.subsets_Grz : 𝐆𝐫𝐳 ⊆ (𝐒𝟒𝐆𝐫𝐳 : Set F) := by aesop;

end Logics

end LO.Modal
