import Foundation.Logic.System
import Foundation.Logic.Axioms

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [System F S]
variable {𝓢 : S} {p q r : F}


def cast (e : p = q) (b : 𝓢 ⊢ p) : 𝓢 ⊢ q := e ▸ b
def cast! (e : p = q) (b : 𝓢 ⊢! p) : 𝓢 ⊢! q := ⟨cast e b.some⟩


class ModusPonens (𝓢 : S) where
  mdp {p q : F} : 𝓢 ⊢ p ➝ q → 𝓢 ⊢ p → 𝓢 ⊢ q

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢! p ➝ q → 𝓢 ⊢! p → 𝓢 ⊢! q := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!

class HasAxiomVerum (𝓢 : S) where
  verum : 𝓢 ⊢ Axioms.Verum

def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := HasAxiomVerum.verum
@[simp] lemma verum! [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := ⟨verum⟩


class HasAxiomImply₁ (𝓢 : S)  where
  imply₁ (p q : F) : 𝓢 ⊢ Axioms.Imply₁ p q

def imply₁ [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ p ➝ q ➝ p := HasAxiomImply₁.imply₁ _ _
@[simp] lemma imply₁! [HasAxiomImply₁ 𝓢] : 𝓢 ⊢! p ➝ q ➝ p := ⟨imply₁⟩

def imply₁' [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢ p) : 𝓢 ⊢ q ➝ p := imply₁ ⨀ h
lemma imply₁'! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢! p) : 𝓢 ⊢! q ➝ p := ⟨imply₁' d.some⟩

@[deprecated imply₁'] def dhyp [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (q : F) (b : 𝓢 ⊢ p) : 𝓢 ⊢ q ➝ p := imply₁' b
@[deprecated imply₁'!] lemma dhyp! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (b : 𝓢 ⊢! p) : 𝓢 ⊢! q ➝ p := ⟨dhyp _ b.some⟩


class HasAxiomImply₂ (𝓢 : S)  where
  imply₂ (p q r : F) : 𝓢 ⊢ Axioms.Imply₂ p q r

def imply₂ [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r := HasAxiomImply₂.imply₂ _ _ _
@[simp] lemma imply₂! [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r := ⟨imply₂⟩

def imply₂' [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢ p ➝ q ➝ r) (d₂ : 𝓢 ⊢ p ➝ q) (d₃ : 𝓢 ⊢ p) : 𝓢 ⊢ r := imply₂ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma imply₂'! [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢! p ➝ q ➝ r) (d₂ : 𝓢 ⊢! p ➝ q) (d₃ : 𝓢 ⊢! p) : 𝓢 ⊢! r := ⟨imply₂' d₁.some d₂.some d₃.some⟩


class HasAxiomAndElim (𝓢 : S)  where
  and₁ (p q : F) : 𝓢 ⊢ Axioms.AndElim₁ p q
  and₂ (p q : F) : 𝓢 ⊢ Axioms.AndElim₂ p q

def and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ p ⋏ q ➝ p := HasAxiomAndElim.and₁ _ _
@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! p ⋏ q ➝ p := ⟨and₁⟩

def and₁' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ p := and₁ ⨀ d
alias andLeft := and₁'

lemma and₁'! [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (p ⋏ q)) : 𝓢 ⊢! p := ⟨and₁' d.some⟩
alias and_left! := and₁'!

def and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ p ⋏ q ➝ q := HasAxiomAndElim.and₂ _ _
@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! p ⋏ q ➝ q := ⟨and₂⟩

def and₂' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ q := and₂ ⨀ d
alias andRight := and₂'

lemma and₂'!  [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (p ⋏ q)) : 𝓢 ⊢! q := ⟨and₂' d.some⟩
alias and_right! := and₂'!


class HasAxiomAndInst (𝓢 : S) where
  and₃ (p q : F) : 𝓢 ⊢ Axioms.AndInst p q

def and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ p ➝ q ➝ p ⋏ q := HasAxiomAndInst.and₃ _ _
@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢! p ➝ q ➝ p ⋏ q := ⟨and₃⟩

def and₃' [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ p) (d₂: 𝓢 ⊢ q) : 𝓢 ⊢ p ⋏ q := and₃ ⨀ d₁ ⨀ d₂
alias andIntro := and₃'

lemma and₃'!  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! p) (d₂: 𝓢 ⊢! q) : 𝓢 ⊢! p ⋏ q := ⟨and₃' d₁.some d₂.some⟩
alias and_intro! := and₃'!


class HasAxiomOrInst (𝓢 : S) where
  or₁ (p q : F) : 𝓢 ⊢ Axioms.OrInst₁ p q
  or₂ (p q : F) : 𝓢 ⊢ Axioms.OrInst₂ p q

def or₁  [HasAxiomOrInst 𝓢] : 𝓢 ⊢ p ➝ p ⋎ q := HasAxiomOrInst.or₁ _ _
@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! p ➝ p ⋎ q := ⟨or₁⟩

def or₁' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ p) : 𝓢 ⊢ p ⋎ q := or₁ ⨀ d
lemma or₁'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! p) : 𝓢 ⊢! p ⋎ q := ⟨or₁' d.some⟩

def or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ q ➝ p ⋎ q := HasAxiomOrInst.or₂ _ _
@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! q ➝ p ⋎ q := ⟨or₂⟩

def or₂' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ q) : 𝓢 ⊢ p ⋎ q := or₂ ⨀ d
lemma or₂'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! q) : 𝓢 ⊢! p ⋎ q := ⟨or₂' d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ (p q r : F) : 𝓢 ⊢ Axioms.OrElim p q r

def or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (p ➝ r) ➝ (q ➝ r) ➝ (p ⋎ q) ➝ r := HasAxiomOrElim.or₃ _ _ _
@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢! (p ➝ r) ➝ (q ➝ r) ➝ (p ⋎ q) ➝ r := ⟨or₃⟩

def or₃'' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ p ➝ r) (d₂ : 𝓢 ⊢ q ➝ r) : 𝓢 ⊢ p ⋎ q ➝ r := or₃ ⨀ d₁ ⨀ d₂
lemma or₃''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! p ➝ r) (d₂ : 𝓢 ⊢! q ➝ r) : 𝓢 ⊢! p ⋎ q ➝ r := ⟨or₃'' d₁.some d₂.some⟩

def or₃''' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ p ➝ r) (d₂ : 𝓢 ⊢ q ➝ r) (d₃ : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ r := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias orCases := or₃'''

lemma or₃'''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! p ➝ r) (d₂ : 𝓢 ⊢! q ➝ r) (d₃ : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! r := ⟨or₃''' d₁.some d₂.some d₃.some⟩
alias or_cases! := or₃'''!


class HasAxiomEFQ (𝓢 : S) where
  efq (p : F) : 𝓢 ⊢ Axioms.EFQ p

def efq [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ p := HasAxiomEFQ.efq _
@[simp] lemma efq! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⊥ ➝ p := ⟨efq⟩

def efq' [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ p := efq ⨀ b
lemma efq'! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! p := ⟨efq' h.some⟩


class HasAxiomLEM (𝓢 : S) where
  lem (p : F) : 𝓢 ⊢ Axioms.LEM p

def lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ p ⋎ ∼p := HasAxiomLEM.lem p
@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢! p ⋎ ∼p := ⟨lem⟩


class HasAxiomDNE (𝓢 : S) where
  dne (p : F) : 𝓢 ⊢ Axioms.DNE p

def dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼p ➝ p := HasAxiomDNE.dne _
@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼∼p ➝ p := ⟨dne⟩

def dne' [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼p) : 𝓢 ⊢ p := dne ⨀ b
lemma dne'! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼∼p) : 𝓢 ⊢! p := ⟨dne' h.some⟩


class HasAxiomWeakLEM (𝓢 : S) where
  wlem (p : F) : 𝓢 ⊢ Axioms.WeakLEM p

def wlem [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢ ∼p ⋎ ∼∼p := HasAxiomWeakLEM.wlem p
@[simp] lemma wlem! [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢! ∼p ⋎ ∼∼p := ⟨wlem⟩


class HasAxiomDummett (𝓢 : S) where
  dummett (p q : F) : 𝓢 ⊢ Axioms.GD p q

def dummett [HasAxiomDummett 𝓢] : 𝓢 ⊢ (p ➝ q) ⋎ (q ➝ p) := HasAxiomDummett.dummett p q
@[simp] lemma dummett! [HasAxiomDummett 𝓢] : 𝓢 ⊢! Axioms.GD p q := ⟨dummett⟩


class HasAxiomPeirce (𝓢 : S) where
  peirce (p q : F) : 𝓢 ⊢ Axioms.Peirce p q

def peirce [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((p ➝ q) ➝ p) ➝ p := HasAxiomPeirce.peirce _ _
@[simp] lemma peirce! [HasAxiomPeirce 𝓢] : 𝓢 ⊢! ((p ➝ q) ➝ p) ➝ p := ⟨peirce⟩


/--
  Negation `∼p` is equivalent to `p ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼p` as an abbreviation of `p ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  neg_equiv (p) : 𝓢 ⊢ Axioms.NegEquiv p

def neg_equiv [NegationEquiv 𝓢] : 𝓢 ⊢ ∼p ⭤ (p ➝ ⊥) := NegationEquiv.neg_equiv _
@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢! ∼p ⭤ (p ➝ ⊥) := ⟨neg_equiv⟩

class HasAxiomElimContra (𝓢 : S)  where
  elim_contra (p q : F) : 𝓢 ⊢ Axioms.ElimContra p q

def elim_contra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((∼q) ➝ (∼p)) ➝ (p ➝ q) := HasAxiomElimContra.elim_contra _ _
@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! (∼q ➝ ∼p) ➝ (p ➝ q)  := ⟨elim_contra⟩


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

def neg_equiv'.mp [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼p → 𝓢 ⊢ p ➝ ⊥ := λ h => (and₁' neg_equiv) ⨀ h
def neg_equiv'.mpr [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ p ➝ ⊥ → 𝓢 ⊢ ∼p := λ h => (and₂' neg_equiv) ⨀ h
lemma neg_equiv'! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼p ↔ 𝓢 ⊢! p ➝ ⊥ := ⟨λ ⟨h⟩ => ⟨neg_equiv'.mp h⟩, λ ⟨h⟩ => ⟨neg_equiv'.mpr h⟩⟩

def iffIntro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ p ➝ q) (b₂ : 𝓢 ⊢ q ➝ p) : 𝓢 ⊢ p ⭤ q := andIntro b₁ b₂
def iff_intro! [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢! p ➝ q) (h₂ : 𝓢 ⊢! q ➝ p) : 𝓢 ⊢! p ⭤ q := ⟨andIntro h₁.some h₂.some⟩

lemma and_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! p ⋏ q ↔ 𝓢 ⊢! p ∧ 𝓢 ⊢! q := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma iff_intro_iff  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! p ⭤ q ↔ 𝓢 ⊢! p ➝ q ∧ 𝓢 ⊢! q ➝ p := ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma provable_iff_of_iff  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! p ↔ 𝓢 ⊢! q := ⟨fun hp ↦ and_left! h ⨀ hp, fun hq ↦ and_right! h ⨀ hq⟩

def impId [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p : F) : 𝓢 ⊢ p ➝ p := imply₂ (p := p) (q := (p ➝ p)) (r := p) ⨀ imply₁ ⨀ imply₁
@[simp] def imp_id! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! p ➝ p := ⟨impId p⟩

def iffId [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p : F) : 𝓢 ⊢ p ⭤ p := and₃' (impId p) (impId p)
@[simp] def iff_id! [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! p ⭤ p := ⟨iffId p⟩

instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] : System.NegationEquiv 𝓢 where
  neg_equiv := by intro p; simp [Axioms.NegEquiv, NegAbbrev.neg]; apply iffId;


def notbot [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := neg_equiv'.mpr (impId ⊥)
@[simp] lemma notbot! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := ⟨notbot⟩

def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ p ➝ q ➝ r) (bq : 𝓢 ⊢ p ➝ q) : 𝓢 ⊢ p ➝ r := imply₂ ⨀ bqr ⨀ bq
lemma mdp₁! [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! p ➝ q ➝ r) (hq : 𝓢 ⊢! p ➝ q) : 𝓢 ⊢! p ➝ r := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ p ➝ q ➝ r ➝ s) (bq : 𝓢 ⊢ p ➝ q ➝ r) : 𝓢 ⊢ p ➝ q ➝ s := dhyp p (imply₂) ⨀₁ bqr ⨀₁ bq
lemma mdp₂! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! p ➝ q ➝ r ➝ s) (hq : 𝓢 ⊢! p ➝ q ➝ r) : 𝓢 ⊢! p ➝ q ➝ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ p ➝ q ➝ r ➝ s ➝ t) (bq : 𝓢 ⊢ p ➝ q ➝ r ➝ s) : 𝓢 ⊢ p ➝ q ➝ r ➝ t := (dhyp p <| dhyp q <| imply₂) ⨀₂ bqr ⨀₂ bq
lemma mdp₃! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! p ➝ q ➝ r ➝ s ➝ t) (hq : 𝓢 ⊢! p ➝ q ➝ r ➝ s) : 𝓢 ⊢! p ➝ q ➝ r ➝ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ p ➝ q ➝ r ➝ s ➝ t ➝ u) (bq : 𝓢 ⊢ p ➝ q ➝ r ➝ s ➝ t) : 𝓢 ⊢ p ➝ q ➝ r ➝ s ➝ u := (dhyp p <| dhyp q <| dhyp r <| imply₂) ⨀₃ bqr ⨀₃ bq
lemma mdp₄! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! p ➝ q ➝ r ➝ s ➝ t ➝ u) (hq : 𝓢 ⊢! p ➝ q ➝ r ➝ s ➝ t) : 𝓢 ⊢! p ➝ q ➝ r ➝ s ➝ u := ⟨mdp₄ hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄
infixl:90 "⨀₄" => mdp₄!

def impTrans'' [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : 𝓢 ⊢ p ➝ q) (bqr : 𝓢 ⊢ q ➝ r) : 𝓢 ⊢ p ➝ r := imply₂ ⨀ dhyp p bqr ⨀ bpq
lemma imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! p ➝ q) (hqr : 𝓢 ⊢! q ➝ r) : 𝓢 ⊢! p ➝ r := ⟨impTrans'' hpq.some hqr.some⟩

lemma unprovable_imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! p ➝ q) : 𝓢 ⊬ p ➝ r → 𝓢 ⊬ q ➝ r := by
  contrapose; simp [neg_neg];
  exact imp_trans''! hpq;

def iffTrans'' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h₁ : 𝓢 ⊢ p ⭤ q) (h₂ : 𝓢 ⊢ q ⭤ r) : 𝓢 ⊢ p ⭤ r := by
  apply iffIntro;
  . exact impTrans'' (and₁' h₁) (and₁' h₂);
  . exact impTrans'' (and₂' h₂) (and₂' h₁);
lemma iff_trans''! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]  (h₁ : 𝓢 ⊢! p ⭤ q) (h₂ : 𝓢 ⊢! q ⭤ r) : 𝓢 ⊢! p ⭤ r := ⟨iffTrans'' h₁.some h₂.some⟩

lemma unprovable_iff! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (H : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊬ p ↔ 𝓢 ⊬ q := by
  constructor;
  . intro hp hq; have := and₂'! H ⨀ hq; contradiction;
  . intro hq hp; have := and₁'! H ⨀ hp; contradiction;

def imply₁₁ [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p q r : F) : 𝓢 ⊢ p ➝ q ➝ r ➝ p := impTrans'' imply₁ imply₁
@[simp] lemma imply₁₁! [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p q r : F) : 𝓢 ⊢! p ➝ q ➝ r ➝ p := ⟨imply₁₁ p q r⟩

-- lemma generalConjFinset! [DecidableEq F] {Γ : Finset F} (h : p ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ p := by simp [Finset.conj, (generalConj! (Finset.mem_toList.mpr h))];

def implyAnd [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bq : 𝓢 ⊢ p ➝ q) (br : 𝓢 ⊢ p ➝ r) : 𝓢 ⊢ p ➝ q ⋏ r := dhyp p and₃ ⨀₁ bq ⨀₁ br
lemma imply_and! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hq : 𝓢 ⊢! p ➝ q) (hr : 𝓢 ⊢! p ➝ r) : 𝓢 ⊢! p ➝ q ⋏ r := ⟨implyAnd hq.some hr.some⟩


def andComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p q : F) : 𝓢 ⊢ p ⋏ q ➝ q ⋏ p := implyAnd and₂ and₁
lemma and_comm! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! p ⋏ q ➝ q ⋏ p := ⟨andComm p q⟩

def andComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ q ⋏ p := andComm _ _ ⨀ h
lemma and_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! p ⋏ q) : 𝓢 ⊢! q ⋏ p := ⟨andComm' h.some⟩


def iffComm  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p q : F) : 𝓢 ⊢ (p ⭤ q) ➝ (q ⭤ p) := andComm _ _
lemma iff_comm!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (p ⭤ q) ➝ (q ⭤ p) := ⟨iffComm p q⟩

def iffComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ p ⭤ q) : 𝓢 ⊢ q ⭤ p := iffComm _ _ ⨀ h
lemma iff_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! q ⭤ p := ⟨iffComm' h.some⟩


def andImplyIffImplyImply [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (p q r : F) : 𝓢 ⊢ (p ⋏ q ➝ r) ⭤ (p ➝ q ➝ r) := by
  let b₁ : 𝓢 ⊢ (p ⋏ q ➝ r) ➝ p ➝ q ➝ r :=
    imply₁₁ (p ⋏ q ➝ r) p q ⨀₃ dhyp (p ⋏ q ➝ r) and₃
  let b₂ : 𝓢 ⊢ (p ➝ q ➝ r) ➝ p ⋏ q ➝ r :=
    imply₁ ⨀₂ (dhyp (p ➝ q ➝ r) and₁) ⨀₂ (dhyp (p ➝ q ➝ r) and₂);
  exact iffIntro b₁ b₂
lemma and_imply_iff_imply_imply! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (p ⋏ q ➝ r) ⭤ (p ➝ q ➝ r) := ⟨andImplyIffImplyImply p q r⟩

def andImplyIffImplyImply'.mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ p ⋏ q ➝ r) : 𝓢 ⊢ p ➝ q ➝ r := (and₁' $ andImplyIffImplyImply p q r) ⨀ d
def andImplyIffImplyImply'.mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ p ➝ q ➝ r) : 𝓢 ⊢ p ⋏ q ➝ r := (and₂' $ andImplyIffImplyImply p q r) ⨀ d

lemma and_imply_iff_imply_imply'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]: (𝓢 ⊢! p ⋏ q ➝ r) ↔ (𝓢 ⊢! p ➝ q ➝ r) := by
  apply Iff.intro;
  . intro ⟨h⟩; exact ⟨andImplyIffImplyImply'.mp h⟩
  . intro ⟨h⟩; exact ⟨andImplyIffImplyImply'.mpr h⟩

def imply_left_verum [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ p ➝ ⊤ := dhyp p verum
@[simp] lemma imply_left_verum! [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! p ➝ ⊤ := ⟨imply_left_verum⟩



instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩


section Conjunction

variable [System.Minimal 𝓢]
variable [DecidableEq F]
variable {Γ Δ : List F}

def generalConj {Γ : List F} {p : F} (h : p ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ p :=
  match Γ with
  | []     => by simp at h
  | q :: Γ =>
    if e : p = q
    then cast (by simp [e]) (and₁ (p := p) (q := Γ.conj))
    else
      have : p ∈ Γ := by simpa [e] using h
      impTrans'' and₂ (generalConj this)
lemma generalConj! (h : p ∈ Γ) : 𝓢 ⊢! Γ.conj ➝ p := ⟨generalConj h⟩

def conjIntro (Γ : List F) (b : (p : F) → p ∈ Γ → 𝓢 ⊢ p) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  | []     => verum
  | q :: Γ => andIntro (b q (by simp)) (conjIntro Γ (fun q hq ↦ b q (by simp [hq])))

def implyConj (p : F) (Γ : List F) (b : (q : F) → q ∈ Γ → 𝓢 ⊢ p ➝ q) : 𝓢 ⊢ p ➝ Γ.conj :=
  match Γ with
  | []     => dhyp p verum
  | q :: Γ => implyAnd (b q (by simp)) (implyConj p Γ (fun q hq ↦ b q (by simp [hq])))

def conjImplyConj (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := implyConj _ _ (fun _ hq ↦ generalConj (h hq))

def generalConj' {Γ : List F} {p : F} (h : p ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ p :=
  match Γ with
  | []     => by simp at h
  | [q]    => by simp_all; exact impId q;
  | q :: r :: Γ => by
    simp;
    by_cases e : p = q;
    . rw [←e]; exact and₁;
    . have : p ∈ (r :: Γ) := by simpa [e] using h;
      exact impTrans'' and₂ (generalConj' this);
lemma generate_conj'! (h : p ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ p := ⟨generalConj' h⟩

def conjIntro' (Γ : List F) (b : (p : F) → p ∈ Γ → 𝓢 ⊢ p) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  | []     => verum
  | [q]    => by apply b; simp;
  | q :: r :: Γ => by
    simp;
    exact andIntro (b q (by simp)) (conjIntro' _ (by aesop))
lemma conj_intro'! (b : (p : F) → p ∈ Γ → 𝓢 ⊢! p) : 𝓢 ⊢! ⋀Γ := ⟨conjIntro' Γ (λ p hp => (b p hp).some)⟩

def implyConj' (p : F) (Γ : List F) (b : (q : F) → q ∈ Γ → 𝓢 ⊢ p ➝ q) : 𝓢 ⊢ p ➝ ⋀Γ :=
  match Γ with
  | []     => dhyp p verum
  | [q]    => by apply b; simp;
  | q :: r :: Γ => by
    simp;
    apply implyAnd (b q (by simp)) (implyConj' p _ (fun q hq ↦ b q (by simp [hq])));
lemma imply_conj'! (p : F) (Γ : List F) (b : (q : F) → q ∈ Γ → 𝓢 ⊢! p ➝ q) : 𝓢 ⊢! p ➝ ⋀Γ := ⟨implyConj' p Γ (λ q hq => (b q hq).some)⟩

def conjImplyConj' {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ➝ ⋀Δ :=
  implyConj' _ _ (fun _ hq ↦ generalConj' (h hq))

end Conjunction

end


section

variable {G T : Type*} [System G T] [LogicalConnective G] {𝓣 : T}

def Minimal.ofEquiv (𝓢 : S) [System.Minimal 𝓢] (𝓣 : T) (φ : G →ˡᶜ F) (e : (p : G) → 𝓢 ⊢ φ p ≃ 𝓣 ⊢ p) : System.Minimal 𝓣 where
  mdp {p q dpq dp} := (e q) (
    let d : 𝓢 ⊢ φ p ➝ φ q := by simpa using (e (p ➝ q)).symm dpq
    d ⨀ ((e p).symm dp))
  neg_equiv p := e _ (by simpa using neg_equiv)
  verum := e _ (by simpa using verum)
  imply₁ p q := e _ (by simpa using imply₁)
  imply₂ p q r := e _ (by simpa using imply₂)
  and₁ p q := e _ (by simpa using and₁)
  and₂ p q := e _ (by simpa using and₂)
  and₃ p q := e _ (by simpa using and₃)
  or₁ p q := e _ (by simpa using or₁)
  or₂ p q := e _ (by simpa using or₂)
  or₃ p q r := e _ (by simpa using or₃)

def Classical.ofEquiv (𝓢 : S) [System.Classical 𝓢] (𝓣 : T) (φ : G →ˡᶜ F) (e : (p : G) → 𝓢 ⊢ φ p ≃ 𝓣 ⊢ p) : System.Classical 𝓣 where
  mdp {p q dpq dp} := (e q) (
    let d : 𝓢 ⊢ φ p ➝ φ q := by simpa using (e (p ➝ q)).symm dpq
    d ⨀ ((e p).symm dp))
  neg_equiv p := e _ (by simpa using neg_equiv)
  verum := e _ (by simpa using verum)
  imply₁ p q := e _ (by simpa using imply₁)
  imply₂ p q r := e _ (by simpa using imply₂)
  and₁ p q := e _ (by simpa using and₁)
  and₂ p q := e _ (by simpa using and₂)
  and₃ p q := e _ (by simpa using and₃)
  or₁ p q := e _ (by simpa using or₁)
  or₂ p q := e _ (by simpa using or₂)
  or₃ p q r := e _ (by simpa using or₃)
  dne p := e _ (by simpa using dne)

end

end LO.System
