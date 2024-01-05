import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

lemma _root_.Set.subset_triunion₁ (s₁ s₂ s₃ : Set F) : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_left _ _) (Set.subset_union_left _ _)

lemma _root_.Set.subset_triunion₂  (s₁ s₂ s₃ : Set F) : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans
  (Set.subset_union_right _ _) (Set.subset_union_left _ _)

lemma _root_.Set.subset_triunion₃ (s₁ s₂ s₃ : Set F) : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.subset_union_right _ _

attribute [simp] Set.Subset.rfl

namespace LO.Modal.Normal

variable {p q : Formula α}

abbrev Logic (α) := Set (Formula α)


abbrev LogicK : Logic α := 𝐊
notation "𝐊" => LogicK.ctx

namespace LogicK

@[simp] lemma includes_AxiomK : (AxiomK p q) ∈ 𝐊 := by simp [LogicK]
@[simp] lemma subsets_AxiomK : 𝐊 ⊆ (𝐊 : Logic α) := by simp [LogicK];

end LogicK


def LogicKD : Logic α := 𝐊 ∪ 𝐃
notation "𝐊𝐃" => LogicKD

/-
abbrev LogicKD4 : Logic α := AxiomK ∪ AxiomD ∪ 𝟒
abbrev LogicKD5 : Logic α := AxiomK ∪ AxiomD ∪ 𝟓
abbrev LogicKDB : Logic α := AxiomK ∪ AxiomD ∪ 𝐁
abbrev LogicKD45 : Logic α := AxiomK ∪ AxiomD ∪ 𝟒 ∪ 𝟓

abbrev LogicKT : Logic α := AxiomK ∪ 𝐓
abbrev LogicKTB : Logic α := AxiomK ∪ AxiomT ∪ 𝐁
abbrev LogicKT4 : Logic α := AxiomK ∪ AxiomT ∪ 𝟒
abbrev LogicKT5 : Logic α := AxiomK ∪ AxiomT ∪ 𝟓

abbrev LogicKB : Logic α := AxiomK ∪ 𝐁
abbrev LogicKB5 : Logic α := AxiomK ∪ 𝐁 ∪ 𝟓

abbrev LogicK4 : Logic α := AxiomK ∪ 𝟒
abbrev LogicK45 : Logic α := AxiomK ∪ 𝟒 ∪ 𝟓

abbrev LogicK5 : Logic α := AxiomK ∪ 𝟓
-/

def LogicKT4 : Logic α := 𝐊 ∪ 𝐓 ∪ 𝟒

@[simp] abbrev LogicS4 {F} := @LogicKT4 F
notation "𝐒𝟒" => LogicS4

namespace LogicS4

@[simp] lemma includes_AxiomK : AxiomK p q ∈ (𝐒𝟒 : Logic α) := by simp [LogicKT4]
@[simp] lemma includes_AxiomT : AxiomT p ∈ (𝐒𝟒 : Logic α) := by simp [LogicKT4]
@[simp] lemma includes_Axiom4 : Axiom4 p ∈ (𝐒𝟒 : Logic α) := by simp [LogicKT4]
@[simp] lemma subsets_K : 𝐊 ⊆ (𝐒𝟒 : Logic α) := by apply Set.subset_triunion₁
@[simp] lemma subsets_T : 𝐓 ⊆ (𝐒𝟒 : Logic α) := by apply Set.subset_triunion₂
@[simp] lemma subsets_4 : 𝟒 ⊆ (𝐒𝟒 : Logic α) := by apply Set.subset_triunion₃

end LogicS4


def LogicS4Dot2 : Logic α := 𝐒𝟒 ∪ .𝟐

notation "𝐒𝟒.𝟐" => LogicS4Dot2

namespace LogicS4Dot2

@[simp] lemma includes_AxiomDot2 : AxiomDot2 p ∈ (𝐒𝟒.𝟐 : Logic α) := by simp [LogicS4Dot2]
@[simp] lemma subsets_Dot2 : AxiomDot2.ctx ⊆ (𝐒𝟒.𝟐 : Logic α) := by simp [LogicS4Dot2]
@[simp] lemma subsets_LogicS4_ctx : 𝐒𝟒 ⊆ (𝐒𝟒.𝟐 : Logic α) := by simp [LogicKT4, LogicS4Dot2]

end LogicS4Dot2


def LogicS4Dot3 : Logic α := 𝐒𝟒 ∪ .𝟑
notation "𝐒𝟒.𝟑" => LogicS4Dot3

namespace LogicS4Dot3

@[simp] lemma includes_AxiomDot3 : AxiomDot3 p q ∈ (𝐒𝟒.𝟑 : Logic α) := by simp [LogicS4Dot3, AxiomDot3.ctx]; aesop;
@[simp] lemma subsets_Dot2 : AxiomDot3.ctx ⊆ (𝐒𝟒.𝟑 : Logic α) := by simp [LogicS4Dot3]
@[simp] lemma subsets_LogicS4_ctx : 𝐒𝟒 ⊆ (𝐒𝟒.𝟑 : Logic α) := by simp [LogicS4Dot3]

end LogicS4Dot3


def LogicS4Grz : Logic α := 𝐒𝟒 ∪ 𝐆𝐫𝐳
notation "𝐒𝟒𝐆𝐫𝐳" => LogicS4Grz

namespace LogicS4Grz

@[simp] lemma includes_AxiomGrz : AxiomGrz p ∈ (𝐒𝟒𝐆𝐫𝐳 : Logic α) := by simp [LogicS4Grz]
@[simp] lemma subsets_Dot2 : AxiomGrz.ctx ⊆ (𝐒𝟒𝐆𝐫𝐳 : Logic α) := by simp [LogicS4Grz]
@[simp] lemma subsets_LogicS4_ctx : 𝐒𝟒 ⊆ (𝐒𝟒𝐆𝐫𝐳 : Logic α) := by simp [LogicS4Grz]

end LogicS4Grz


def LogicKT5 : Logic α := 𝐊 ∪ 𝐓 ∪ 𝟓

@[simp] abbrev LogicS5 {F} := @LogicKT5 F
notation "𝐒𝟓" => LogicS5

namespace LogicS5

@[simp] lemma includes_AxiomK : AxiomK p q ∈ (𝐒𝟓 : Logic α) := by simp [LogicKT5]
@[simp] lemma includes_AxiomT : AxiomT p ∈ (𝐒𝟓 : Logic α) := by simp [LogicKT5]
@[simp] lemma includes_Axiom5 : Axiom5 p ∈ (𝐒𝟓 : Logic α) := by simp [LogicKT5]
@[simp] lemma subsets_K : 𝐊 ⊆ (𝐒𝟓 : Logic α) := by apply Set.subset_triunion₁
@[simp] lemma subsets_T : 𝐓 ⊆ (𝐒𝟓 : Logic α) := by apply Set.subset_triunion₂
@[simp] lemma subsets_5 : 𝟓 ⊆ (𝐒𝟓 : Logic α) := by apply Set.subset_triunion₃

end LogicS5


def LogicGL : Logic α := 𝐊 ∪ 𝐋
notation "𝐆𝐋" => LogicGL

namespace LogicGL

@[simp] lemma includes_AxiomK : AxiomK p q ∈ (𝐆𝐋 : Logic α) := by simp [LogicGL]
@[simp] lemma includes_AxiomL : AxiomL p ∈ (𝐆𝐋 : Logic α) := by simp [LogicGL]
@[simp] lemma subsets_K : 𝐊 ⊆ (𝐆𝐋 : Logic α) := by simp [LogicGL, LogicK]
@[simp] lemma subsets_L : 𝐋 ⊆ (𝐆𝐋 : Logic α) := by simp [LogicGL]
@[simp] lemma subsets_LogicK_ctx : 𝐊 ⊆ (𝐆𝐋 : Logic α) := by simp [LogicK, LogicGL]

end LogicGL

end LO.Modal.Normal
