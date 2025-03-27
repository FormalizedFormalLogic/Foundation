import Foundation.Logic.Entailment
import Foundation.Logic.Axioms

/-!
# Basic Lemmata of Hilbert-Style Deduction System.

## Naming Convention

The names of the formalized proofs are determined by the following steps. (e.g. `𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ)`):
1. Convert the formula to Łukasiewicz's notation (`ECKφψχCφCψχ`).
2. Remove meta variables (`ECKCC`).
3. Make it lowerCamelCase (`eCKCC`).
4. Postfix `!` if it is a proposition (`eCKCC!`).
-/

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
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

def cOfConseq [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := imply₁ ⨀ h
alias dhyp := cOfConseq

lemma c!_of_conseq! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := ⟨cOfConseq d.some⟩
alias dhyp! := c!_of_conseq!

class HasAxiomImply₂ (𝓢 : S)  where
  imply₂ (φ ψ χ : F) : 𝓢 ⊢ Axioms.Imply₂ φ ψ χ

def imply₂ [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := HasAxiomImply₂.imply₂ _ _ _
@[simp] lemma imply₂! [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ⟨imply₂⟩

class HasAxiomAndElim (𝓢 : S)  where
  and₁ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₁ φ ψ
  and₂ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₂ φ ψ

def and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ φ := HasAxiomAndElim.and₁ _ _
@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ φ := ⟨and₁⟩

def ofKLeft [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := and₁ ⨀ d
alias andLeft := ofKLeft

lemma of_k!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! φ := ⟨ofKLeft d.some⟩
alias and_left := of_k!_left

def and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := HasAxiomAndElim.and₂ _ _
@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ := ⟨and₂⟩

def ofKRight [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := and₂ ⨀ d
alias andRight := ofKRight

lemma of_k_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! ψ := ⟨ofKRight d.some⟩
alias and_right := of_k_right


class HasAxiomAndInst (𝓢 : S) where
  and₃ (φ ψ : F) : 𝓢 ⊢ Axioms.AndInst φ ψ

def and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := HasAxiomAndInst.and₃ _ _
@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢! φ ➝ ψ ➝ φ ⋏ ψ := ⟨and₃⟩

def kIntro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂

lemma k!_intro  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := ⟨kIntro d₁.some d₂.some⟩


class HasAxiomOrInst (𝓢 : S) where
  or₁ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₁ φ ψ
  or₂ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₂ φ ψ

def or₁  [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ➝ φ ⋎ ψ := HasAxiomOrInst.or₁ _ _
@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! φ ➝ φ ⋎ ψ := ⟨or₁⟩

def aOfLeft [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := or₁ ⨀ d
lemma a!_of_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := ⟨aOfLeft d.some⟩

def or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := HasAxiomOrInst.or₂ _ _
@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢! ψ ➝ φ ⋎ ψ := ⟨or₂⟩

def aOfRight [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := or₂ ⨀ d
lemma a!_of_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨aOfRight d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ (φ ψ χ : F) : 𝓢 ⊢ Axioms.OrElim φ ψ χ

def or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := HasAxiomOrElim.or₃ _ _ _
@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := ⟨or₃⟩

def cAOfCOfC [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ := or₃ ⨀ d₁ ⨀ d₂
lemma cA!_of_c!_of_c! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ := ⟨cAOfCOfC d₁.some d₂.some⟩

def ofCOfCOfA [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias orCases := ofCOfCOfA

lemma of_c!_of_c!_of_a! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := ⟨ofCOfCOfA d₁.some d₂.some d₃.some⟩
alias or_cases! := of_c!_of_c!_of_a!


class HasAxiomEFQ (𝓢 : S) where
  efq (φ : F) : 𝓢 ⊢ Axioms.EFQ φ

def efq [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := HasAxiomEFQ.efq _
@[simp] lemma efq! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⊥ ➝ φ := ⟨efq⟩

def ofO [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := efq ⨀ b
lemma of_o! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := ⟨ofO h.some⟩


class HasAxiomLEM (𝓢 : S) where
  lem (φ : F) : 𝓢 ⊢ Axioms.LEM φ

def lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := HasAxiomLEM.lem φ
@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢! φ ⋎ ∼φ := ⟨lem⟩


class HasAxiomDNE (𝓢 : S) where
  dne (φ : F) : 𝓢 ⊢ Axioms.DNE φ

def dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ := HasAxiomDNE.dne _
@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼∼φ ➝ φ := ⟨dne⟩

def ofNn [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := dne ⨀ b
lemma of_nn! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := ⟨ofNn h.some⟩

/--
  Negation `∼φ` is equivalent to `φ ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  negEquiv (φ) : 𝓢 ⊢ Axioms.NegEquiv φ

def negEquiv [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ (φ ➝ ⊥) := NegationEquiv.negEquiv _
@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ⭤ (φ ➝ ⊥) := ⟨negEquiv⟩

class HasAxiomElimContra (𝓢 : S)  where
  elimContra (φ ψ : F) : 𝓢 ⊢ Axioms.ElimContra φ ψ

def elimContra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((∼ψ) ➝ (∼φ)) ➝ (φ ➝ ψ) := HasAxiomElimContra.elimContra _ _
@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elimContra⟩

protected class Minimal (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImply₁ 𝓢, HasAxiomImply₂ 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

protected class Intuitionistic (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomEFQ 𝓢

protected class Classical (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomDNE 𝓢


section

variable [ModusPonens 𝓢]

def cOOfN [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ → 𝓢 ⊢ φ ➝ ⊥ := λ h => (ofKLeft negEquiv) ⨀ h
def nOfCO [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ φ ➝ ⊥ → 𝓢 ⊢ ∼φ := λ h => (ofKRight negEquiv) ⨀ h
lemma n!_iff_cO! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ↔ 𝓢 ⊢! φ ➝ ⊥ := ⟨λ ⟨h⟩ => ⟨cOOfN h⟩, λ ⟨h⟩ => ⟨nOfCO h⟩⟩

def eIntro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ φ ➝ ψ) (b₂ : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ φ ⭤ ψ := kIntro b₁ b₂
def e!_intro [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢! φ ➝ ψ) (h₂ : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! φ ⭤ ψ := ⟨kIntro h₁.some h₂.some⟩

lemma k!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ↔ 𝓢 ⊢! φ ∧ 𝓢 ⊢! ψ := ⟨fun h ↦ ⟨and_left h, and_right h⟩, fun h ↦ k!_intro h.1 h.2⟩

lemma e!_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⭤ ψ ↔ 𝓢 ⊢! φ ➝ ψ ∧ 𝓢 ⊢! ψ ➝ φ := ⟨fun h ↦ ⟨and_left h, and_right h⟩, fun h ↦ k!_intro h.1 h.2⟩

lemma provable_iff_of_e!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ↔ 𝓢 ⊢! ψ := ⟨fun hp ↦ and_left h ⨀ hp, fun hq ↦ and_right h ⨀ hq⟩

def cId [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ➝ φ := imply₂ (φ := φ) (ψ := (φ ➝ φ)) (χ := φ) ⨀ imply₁ ⨀ imply₁
@[simp] def c!_id [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ➝ φ := ⟨cId φ⟩

def eId [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ⭤ φ := kIntro (cId φ) (cId φ)
@[simp] def e!_id [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⭤ φ := ⟨eId φ⟩

instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  negEquiv := by intro φ; simp [Axioms.NegEquiv, NegAbbrev.neg]; apply eId;


def nO [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ := nOfCO (cId ⊥)
@[simp] lemma nO! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ := ⟨nO⟩

def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ) (bq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ bqr ⨀ bq
lemma mdp₁! [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ) (hq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ χ := ⟨mdp₁ hqr.some hq.some⟩

infixl:90 "⨀₁" => mdp₁
infixl:90 "⨀₁" => mdp₁!

def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ s := cOfConseq (imply₂) ⨀₁ bqr ⨀₁ bq
lemma mdp₂! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ➝ s := ⟨mdp₂ hqr.some hq.some⟩

infixl:90 "⨀₂" => mdp₂
infixl:90 "⨀₂" => mdp₂!

def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ t := (cOfConseq <| cOfConseq <| imply₂) ⨀₂ bqr ⨀₂ bq
lemma mdp₃! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ t := ⟨mdp₃ hqr.some hq.some⟩

infixl:90 "⨀₃" => mdp₃
infixl:90 "⨀₃" => mdp₃!

def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (bq : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s ➝ u := (cOfConseq <| cOfConseq <| cOfConseq <| imply₂) ⨀₃ bqr ⨀₃ bq
lemma mdp₄! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t ➝ u) (hq : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ t) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ s ➝ u := ⟨mdp₄ hqr.some hq.some⟩
infixl:90 "⨀₄" => mdp₄
infixl:90 "⨀₄" => mdp₄!

def cTrans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : 𝓢 ⊢ φ ➝ ψ) (bqr : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ➝ χ := imply₂ ⨀ cOfConseq bqr ⨀ bpq
lemma c!_trans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) (hqr : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ➝ χ := ⟨cTrans hpq.some hqr.some⟩

lemma unprovable_c!_trans [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊬ φ ➝ χ → 𝓢 ⊬ ψ ➝ χ := by
  contrapose; simp [neg_neg];
  exact c!_trans hpq;

def eTrans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h₁ : 𝓢 ⊢ φ ⭤ ψ) (h₂ : 𝓢 ⊢ ψ ⭤ χ) : 𝓢 ⊢ φ ⭤ χ := by
  apply eIntro;
  . exact cTrans (ofKLeft h₁) (ofKLeft h₂);
  . exact cTrans (ofKRight h₂) (ofKRight h₁);
lemma e!_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]  (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⭤ χ := ⟨eTrans h₁.some h₂.some⟩

lemma unprovable_iff_of_e! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (H : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  . intro hp hq; have := of_k_right H ⨀ hq; contradiction;
  . intro hq hp; have := of_k!_left H ⨀ hp; contradiction;

def cCCC [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ φ := cTrans imply₁ imply₁
@[simp] lemma cCCC! [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢! φ ➝ ψ ➝ χ ➝ φ := ⟨cCCC φ ψ χ⟩

def cKOfCOfC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bq : 𝓢 ⊢ φ ➝ ψ) (br : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := cOfConseq and₃ ⨀₁ bq ⨀₁ br
lemma cK!_of_c!_of_c! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨cKOfCOfC hq.some hr.some⟩


def cKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ φ ⋏ ψ ➝ ψ ⋏ φ := cKOfCOfC and₂ and₁
lemma cKK! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ⋏ ψ ➝ ψ ⋏ φ := ⟨cKK φ ψ⟩

def kSymm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ := cKK _ _ ⨀ h
lemma k!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ := ⟨kSymm h.some⟩


def cEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ : F) : 𝓢 ⊢ (φ ⭤ ψ) ➝ (ψ ⭤ φ) := cKK _ _
lemma cEE!  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⭤ ψ) ➝ (ψ ⭤ φ) := ⟨cEE φ ψ⟩

def eSymm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ⭤ φ := cEE _ _ ⨀ h
lemma e!_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ⭤ φ := ⟨eSymm h.some⟩


def eCKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := by
  let b₁ : 𝓢 ⊢ (φ ⋏ ψ ➝ χ) ➝ φ ➝ ψ ➝ χ :=
    cCCC (φ ⋏ ψ ➝ χ) φ ψ ⨀₃ cOfConseq (ψ := φ ⋏ ψ ➝ χ) and₃
  let b₂ : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ φ ⋏ ψ ➝ χ :=
    imply₁ ⨀₂ (cOfConseq (ψ := φ ➝ ψ ➝ χ) and₁) ⨀₂ (cOfConseq (ψ := φ ➝ ψ ➝ χ) and₂);
  exact eIntro b₁ b₂
lemma eCKCC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ⋏ ψ ➝ χ) ⭤ (φ ➝ ψ ➝ χ) := ⟨eCKCC φ ψ χ⟩

def cCOfCK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ➝ χ := (ofKLeft $ eCKCC φ ψ χ) ⨀ d
def cKOfCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ := (ofKRight $ eCKCC φ ψ χ) ⨀ d

lemma cK!_iff_cC! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]: (𝓢 ⊢! φ ⋏ ψ ➝ χ) ↔ (𝓢 ⊢! φ ➝ ψ ➝ χ) := by
  apply Iff.intro;
  . intro ⟨h⟩; exact ⟨cCOfCK h⟩
  . intro ⟨h⟩; exact ⟨cKOfCC h⟩

def cV [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ⊤ := cOfConseq verum
@[simp] lemma cV! [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! φ ➝ ⊤ := ⟨cV⟩

instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩

section Conjunction

variable [Entailment.Minimal 𝓢]

def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢ ⋀Γ ➝ Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => cId ψ
  | φ :: ψ :: Γ,     0, _  => and₁
  | φ :: ψ :: Γ, n + 1, hn => cTrans (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

def conj₂_nth! (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢! ⋀Γ ➝ Γ[n] := ⟨conj₂Nth Γ n hn⟩

variable {Γ Δ : List F}

def cConj [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then cast (by simp [e]) (and₁ (φ := φ) (ψ := Γ.conj))
    else
      have : φ ∈ Γ := by simpa [e] using h
      cTrans and₂ (cConj this)
lemma cConj!_of_mem [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj ➝ φ := ⟨cConj h⟩

def conjIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  |     [] => verum
  | ψ :: Γ => kIntro (b ψ (by simp)) (conjIntro Γ (fun ψ hq ↦ b ψ (by simp [hq])))

def cConjOfC (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ Γ.conj :=
  match Γ with
  |     [] => cOfConseq verum
  | ψ :: Γ => cKOfCOfC (b ψ (by simp)) (cConjOfC φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))
def cConj!_of_c! (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ Γ.conj := ⟨cConjOfC φ Γ fun ψ h ↦ (b ψ h).get⟩

def cConjConj [DecidableEq F] (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := cConjOfC _ _ (fun _ hq ↦ cConj (h hq))

def cConj₂ [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length h
  have : Γ[Γ.idxOf φ] = φ := List.getElem_idxOf this
  cast (by rw[this]) <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)
lemma cConj₂! [DecidableEq F] (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := ⟨cConj₂ h⟩

def conj₂Intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  |          [] => verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    exact kIntro (b ψ (by simp)) (conj₂Intro _ (by aesop))
lemma conj₂!_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ := ⟨conj₂Intro Γ (λ φ hp => (b φ hp).some)⟩

def cConj₂OfC (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ⋀Γ :=
  match Γ with
  |          [] => cOfConseq verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp;
    apply cKOfCOfC (b ψ (by simp)) (cConj₂OfC φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
lemma cConj₂!_of_c! (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ ⋀Γ := ⟨cConj₂OfC φ Γ (λ ψ hq => (b ψ hq).some)⟩

def cConj₂Conj₂ [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ➝ ⋀Δ :=
  cConj₂OfC _ _ (fun _ hq ↦ cConj₂ (h hq))

end Conjunction

end


section

variable {G T : Type*} [Entailment G T] [LogicalConnective G] {𝓣 : T}

def Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : Entailment.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)

def Classical.ofEquiv (𝓢 : S) [Entailment.Classical 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) : Entailment.Classical 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ➝ f ψ := by simpa using (e (φ ➝ ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
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

end LO.Entailment
