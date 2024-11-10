import Foundation.Logic.System
import Foundation.Logic.Axioms

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [System F S]
variable {𝓢 : S} {φ ψ χ : F}


def cast (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := e ▸ b
def cast! (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := ⟨cast e b.some⟩


class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!

class HasAxiomVerum (𝓢 : S) where
  verum : 𝓢 ⊢ Axioms.Verum

def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := HasAxiomVerum.verum
@[simp] lemma verum! [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := ⟨verum⟩


class HasAxiomImply₁ (𝓢 : S)  where
  imply₁ (φ ψ : F) : 𝓢 ⊢ Axioms.Imply₁ φ ψ

def imply₁ [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ := HasAxiomImply₁.imply₁ _ _
@[simp] lemma imply₁! [HasAxiomImply₁ 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ φ := ⟨imply₁⟩

def imply₁' [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := imply₁ ⨀ h
lemma imply₁'! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := ⟨imply₁' d.some⟩

@[deprecated imply₁'] def dhyp [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (ψ : F) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := imply₁' b


class HasAxiomImply₂ (𝓢 : S)  where
  imply₂ (φ ψ χ : F) : 𝓢 ⊢ Axioms.Imply₂ φ ψ χ

def imply₂ [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := HasAxiomImply₂.imply₂ _ _ _
@[simp] lemma imply₂! [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ⟨imply₂⟩

def imply₂' [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢ φ ➝ ψ ➝ χ) (d₂ : 𝓢 ⊢ φ ➝ ψ) (d₃ : 𝓢 ⊢ φ) : 𝓢 ⊢ χ := imply₂ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma imply₂'! [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢! φ ➝ ψ ➝ χ) (d₂ : 𝓢 ⊢! φ ➝ ψ) (d₃ : 𝓢 ⊢! φ) : 𝓢 ⊢! χ := ⟨imply₂' d₁.some d₂.some d₃.some⟩


class HasAxiomAndElim (𝓢 : S)  where
  and₁ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₁ φ ψ
  and₂ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₂ φ ψ

def and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ φ := HasAxiomAndElim.and₁ _ _
@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ φ := ⟨and₁⟩

def and₁' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := and₁ ⨀ d
alias andLeft := and₁'

lemma and₁'! [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! φ := ⟨and₁' d.some⟩
alias and_left! := and₁'!

def and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := HasAxiomAndElim.and₂ _ _
@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ := ⟨and₂⟩

def and₂' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := and₂ ⨀ d
alias andRight := and₂'

lemma and₂'!  [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! ψ := ⟨and₂' d.some⟩
alias and_right! := and₂'!


class HasAxiomAndInst (𝓢 : S) where
  and₃ (φ ψ : F) : 𝓢 ⊢ Axioms.AndInst φ ψ

def and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := HasAxiomAndInst.and₃ _ _
@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ φ ⋏ ψ := ⟨and₃⟩

def and₃' [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂
alias andIntro := and₃'

lemma and₃'!  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := ⟨and₃' d₁.some d₂.some⟩
alias and_intro! := and₃'!


class HasAxiomOrInst (𝓢 : S) where
  or₁ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₁ φ ψ
  or₂ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₂ φ ψ

def or₁  [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ➝ φ ⋎ ψ := HasAxiomOrInst.or₁ _ _
@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! φ ➝ φ ⋎ ψ := ⟨or₁⟩

def or₁' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := or₁ ⨀ d
lemma or₁'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := ⟨or₁' d.some⟩

def or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := HasAxiomOrInst.or₂ _ _
@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! ψ ➝ φ ⋎ ψ := ⟨or₂⟩

def or₂' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := or₂ ⨀ d
lemma or₂'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨or₂' d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ (φ ψ χ : F) : 𝓢 ⊢ Axioms.OrElim φ ψ χ

def or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := HasAxiomOrElim.or₃ _ _ _
@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := ⟨or₃⟩

def or₃'' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ := or₃ ⨀ d₁ ⨀ d₂
lemma or₃''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ := ⟨or₃'' d₁.some d₂.some⟩

def or₃''' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias orCases := or₃'''

lemma or₃'''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := ⟨or₃''' d₁.some d₂.some d₃.some⟩
alias or_cases! := or₃'''!


class HasAxiomEFQ (𝓢 : S) where
  efq (φ : F) : 𝓢 ⊢ Axioms.EFQ φ

def efq [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := HasAxiomEFQ.efq _
@[simp] lemma efq! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⊥ ➝ φ := ⟨efq⟩

def efq' [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := efq ⨀ b
lemma efq'! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := ⟨efq' h.some⟩


class HasAxiomLEM (𝓢 : S) where
  lem (φ : F) : 𝓢 ⊢ Axioms.LEM φ

def lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := HasAxiomLEM.lem φ
@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢! φ ⋎ ∼φ := ⟨lem⟩


class HasAxiomDNE (𝓢 : S) where
  dne (φ : F) : 𝓢 ⊢ Axioms.DNE φ

def dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ := HasAxiomDNE.dne _
@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼∼φ ➝ φ := ⟨dne⟩

def dne' [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := dne ⨀ b
lemma dne'! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := ⟨dne' h.some⟩


class HasAxiomWeakLEM (𝓢 : S) where
  wlem (φ : F) : 𝓢 ⊢ Axioms.WeakLEM φ

def wlem [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢ ∼φ ⋎ ∼∼φ := HasAxiomWeakLEM.wlem φ
@[simp] lemma wlem! [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢! ∼φ ⋎ ∼∼φ := ⟨wlem⟩


class HasAxiomDummett (𝓢 : S) where
  dummett (φ ψ : F) : 𝓢 ⊢ Axioms.Dummett φ ψ

def dummett [HasAxiomDummett 𝓢] : 𝓢 ⊢ (φ ➝ ψ) ⋎ (ψ ➝ φ) := HasAxiomDummett.dummett φ ψ
@[simp] lemma dummett! [HasAxiomDummett 𝓢] : 𝓢 ⊢! Axioms.Dummett φ ψ := ⟨dummett⟩


class HasAxiomPeirce (𝓢 : S) where
  peirce (φ ψ : F) : 𝓢 ⊢ Axioms.Peirce φ ψ

def peirce [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ ➝ ψ) ➝ φ) ➝ φ := HasAxiomPeirce.peirce _ _
@[simp] lemma peirce! [HasAxiomPeirce 𝓢] : 𝓢 ⊢! ((φ ➝ ψ) ➝ φ) ➝ φ := ⟨peirce⟩


/--
  Negation `∼φ` is equivalent to `φ ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  neg_equiv (φ) : 𝓢 ⊢ Axioms.NegEquiv φ

def neg_equiv [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ (φ ➝ ⊥) := NegationEquiv.neg_equiv _
@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ⭤ (φ ➝ ⊥) := ⟨neg_equiv⟩

class HasAxiomElimContra (𝓢 : S)  where
  elim_contra (φ ψ : F) : 𝓢 ⊢ Axioms.ElimContra φ ψ

def elim_contra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((∼ψ) ➝ (∼φ)) ➝ (φ ➝ ψ) := HasAxiomElimContra.elim_contra _ _
@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elim_contra⟩


protected class Minimal (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImply₁ 𝓢, HasAxiomImply₂ 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

protected class Intuitionistic (𝓢 : S) extends System.Minimal 𝓢, HasAxiomEFQ 𝓢

protected class Classical (𝓢 : S) extends System.Minimal 𝓢, HasAxiomDNE 𝓢


section

variable [ModusPonens 𝓢]

def neg_equiv'.mp [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ → 𝓢 ⊢ φ ➝ ⊥ := λ h => (and₁' neg_equiv) ⨀ h
def neg_equiv'.mpr [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ φ ➝ ⊥ → 𝓢 ⊢ ∼φ := λ h => (and₂' neg_equiv) ⨀ h
lemma neg_equiv'! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ↔ 𝓢 ⊢! φ ➝ ⊥ := ⟨λ ⟨h⟩ => ⟨neg_equiv'.mp h⟩, λ ⟨h⟩ => ⟨neg_equiv'.mpr h⟩⟩

def iffIntro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ φ ➝ ψ) (b₂ : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ φ ⭤ ψ := andIntro b₁ b₂
def iff_intro! [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢! φ ➝ ψ) (h₂ : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! φ ⭤ ψ := ⟨andIntro h₁.some h₂.some⟩

lemma and_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ↔ 𝓢 ⊢! φ ∧ 𝓢 ⊢! ψ := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma iff_intro_iff  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⭤ ψ ↔ 𝓢 ⊢! φ ➝ ψ ∧ 𝓢 ⊢! ψ ➝ φ := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma provable_iff_of_iff  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ↔ 𝓢 ⊢! ψ := ⟨fun hp ↦ and_left! h ⨀ hp, fun hq ↦ and_right! h ⨀ hq⟩

def impId [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ➝ φ := imply₂ (φ := φ) (ψ := (φ ➝ φ)) (χ := φ) ⨀ imply₁ ⨀ imply₁
@[simp] def imp_id! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ➝ φ := ⟨impId φ⟩

def iffId [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ⭤ φ := and₃' (impId φ) (impId φ)
@[simp] def iff_id! [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⭤ φ := ⟨iffId φ⟩

instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] : System.NegationEquiv 𝓢 where
  neg_equiv := by intro φ; simp [Axioms.NegEquiv, NegAbbrev.neg]; apply iffId;


def notbot [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := neg_equiv'.mpr (impId ⊥)
@[simp] lemma notbot! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := ⟨notbot⟩

def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ) (bq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ bqr ⨀ bq
lemma mdp₁! [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ) (hq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ χ := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ s := imply₁' (imply₂) ⨀₁ bqr ⨀₁ bq
lemma mdp₂! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ➝ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ t := (imply₁' <| imply₁' <| imply₂) ⨀₂ bqr ⨀₂ bq
lemma mdp₃! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ u := (imply₁' <| imply₁' <| imply₁' <| imply₂) ⨀₃ bqr ⨀₃ bq
lemma mdp₄! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ u := ⟨mdp₄ hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄
infixl:90 "⨀₄" => mdp₄!

def impTrans'' [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : 𝓢 ⊢ φ ➝ ψ) (bqr : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ imply₁' bqr ⨀ bpq
lemma imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) (hqr : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ➝ χ := ⟨impTrans'' hpq.some hqr.some⟩

lemma unprovable_imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊬ φ ➝ χ → 𝓢 ⊬ ψ ➝ χ := by
  contrapose; simp [neg_neg];
  exact imp_trans''! hpq;

def iffTrans'' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h₁ : 𝓢 ⊢ φ ⭤ ψ) (h₂ : 𝓢 ⊢ ψ ⭤ χ) : 𝓢 ⊢ φ ⭤ χ := by
  apply iffIntro;
  . exact impTrans'' (and₁' h₁) (and₁' h₂);
  . exact impTrans'' (and₂' h₂) (and₂' h₁);
lemma iff_trans''! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]  (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⭤ χ := ⟨iffTrans'' h₁.some h₂.some⟩

lemma unprovable_iff! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (H : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  . intro hp hq; have := and₂'! H ⨀ hq; contradiction;
  . intro hq hp; have := and₁'! H ⨀ hp; contradiction;

def imply₁₁ [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ φ := impTrans'' imply₁ imply₁
@[simp] lemma imply₁₁! [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ φ := ⟨imply₁₁ φ ψ χ⟩

-- lemma generalConjFinset! [DecidableEq F] {Γ : Finset F} (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := by simp [Finset.conj, (generalConj! (Finset.mem_toList.mpr h))];

def implyAnd [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bq : 𝓢 ⊢ φ ➝ ψ) (br : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := imply₁' and₃ ⨀₁ bq ⨀₁ br
lemma imply_and! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨implyAnd hq.some hr.some⟩


def andComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ φ ⋏ ψ ➝ ψ ⋏ φ := implyAnd and₂ and₁
lemma and_comm! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ ⋏ φ := ⟨andComm φ ψ⟩

def andComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := andComm _ _ ⨀ h
lemma and_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ := ⟨andComm' h.some⟩


def iffComm  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ (φ ⭤ ψ) ➝ (ψ ⭤ φ) := andComm _ _
lemma iff_comm!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⭤ ψ) ➝ (ψ ⭤ φ) := ⟨iffComm φ ψ⟩

def iffComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ⭤ φ := iffComm _ _ ⨀ h
lemma iff_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ⭤ φ := ⟨iffComm' h.some⟩


def andImplyIffImplyImply [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := by
  let b₁ : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ➝ φ ➝ ψ ➝ χ :=
    imply₁₁ (φ ⋏ ψ ➝ χ) φ ψ ⨀₃ imply₁' (ψ := φ ⋏ ψ ➝ χ) and₃
  let b₂ : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ φ ⋏ ψ ➝ χ :=
    imply₁ ⨀₂ (imply₁' (ψ := φ ➝ ψ ➝ χ) and₁) ⨀₂ (imply₁' (ψ := φ ➝ ψ ➝ χ) and₂);
  exact iffIntro b₁ b₂
lemma and_imply_iff_imply_imply! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := ⟨andImplyIffImplyImply φ ψ χ⟩

def andImplyIffImplyImply'.mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ χ := (and₁' $ andImplyIffImplyImply φ ψ χ) ⨀ d
def andImplyIffImplyImply'.mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ := (and₂' $ andImplyIffImplyImply φ ψ χ) ⨀ d

lemma and_imply_iff_imply_imply'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]: (𝓢 ⊢! φ ⋏ ψ ➝ χ) ↔ (𝓢 ⊢! φ ➝ ψ ➝ χ) := by
  apply Iff.intro;
  . intro ⟨h⟩; exact ⟨andImplyIffImplyImply'.mp h⟩
  . intro ⟨h⟩; exact ⟨andImplyIffImplyImply'.mpr h⟩

def imply_left_verum [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ⊤ := imply₁' verum
@[simp] lemma imply_left_verum! [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! φ ➝ ⊤ := ⟨imply_left_verum⟩



instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩


section Conjunction

variable [System.Minimal 𝓢]

def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢ ⋀Γ ➝ Γ[n]
  | [],          _,     hn => by simp at hn
  | [ψ],         0,     _  => impId ψ
  | φ :: ψ :: Γ, 0,     _  => and₁
  | φ :: ψ :: Γ, n + 1, hn => impTrans'' (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

def conj₂_nth! (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢! ⋀Γ ➝ Γ[n] := ⟨conj₂Nth Γ n hn⟩

variable [DecidableEq F]
variable {Γ Δ : List F}

def generalConj {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ :=
  match Γ with
  | []     => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then cast (by simp [e]) (and₁ (φ := φ) (ψ := Γ.conj))
    else
      have : φ ∈ Γ := by simpa [e] using h
      impTrans'' and₂ (generalConj this)
lemma generalConj! (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj ➝ φ := ⟨generalConj h⟩

def conjIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  | []     => verum
  | ψ :: Γ => andIntro (b ψ (by simp)) (conjIntro Γ (fun ψ hq ↦ b ψ (by simp [hq])))

def implyConj (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ Γ.conj :=
  match Γ with
  | []     => imply₁' verum
  | ψ :: Γ => implyAnd (b ψ (by simp)) (implyConj φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))

def conjImplyConj (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := implyConj _ _ (fun _ hq ↦ generalConj (h hq))

def generalConj' {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ :=
  have : Γ.indexOf φ < Γ.length := List.indexOf_lt_length.mpr h
  have : Γ[Γ.indexOf φ] = φ := List.getElem_indexOf this
  cast (by rw[this]) <| conj₂Nth Γ (Γ.indexOf φ) (by assumption)
lemma generate_conj'! (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := ⟨generalConj' h⟩

def conjIntro' (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  | []     => verum
  | [ψ]    => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    exact andIntro (b ψ (by simp)) (conjIntro' _ (by aesop))
omit [DecidableEq F] in
lemma conj_intro'! (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ := ⟨conjIntro' Γ (λ φ hp => (b φ hp).some)⟩

def implyConj' (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ⋀Γ :=
  match Γ with
  | []     => imply₁' verum
  | [ψ]    => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    apply implyAnd (b ψ (by simp)) (implyConj' φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
omit [DecidableEq F] in
lemma imply_conj'! (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ ⋀Γ := ⟨implyConj' φ Γ (λ ψ hq => (b ψ hq).some)⟩

def conjImplyConj' {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ➝ ⋀Δ :=
  implyConj' _ _ (fun _ hq ↦ generalConj' (h hq))

end Conjunction

end


section

variable {G T : Type*} [System G T] [LogicalConnective G] {𝓣 : T}

def Minimal.ofEquiv (𝓢 : S) [System.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : System.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  neg_equiv φ := e _ (by simpa using neg_equiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)

def Classical.ofEquiv (𝓢 : S) [System.Classical 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : System.Classical 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  neg_equiv φ := e _ (by simpa using neg_equiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)
  dne φ := e _ (by simpa using dne)

end

end LO.System
