import Logic.Modal.Normal.Formula

namespace LO.Modal.Normal

variable {F : Type u} [ModalLogicSymbol F] (p q : F)

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


end LO.Modal.Normal
