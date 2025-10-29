import Foundation.Logic.Entailment
import Foundation.Propositional.Axioms

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}


class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdp := ModusPonens.mdp
infixl:90 "⨀" => mdp

lemma mdp! [ModusPonens 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp!
infixl:90 "⨀!" => mdp!


/--
  Negation `∼φ` is equivalent to `φ ➝ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ➝ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  negEquiv {φ : F} : 𝓢 ⊢! Axioms.NegEquiv φ
export NegationEquiv (negEquiv)

@[simp] lemma neg_equiv! [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ (φ ➝ ⊥) := ⟨negEquiv⟩


class HasAxiomVerum (𝓢 : S) where
  verum : 𝓢 ⊢! Axioms.Verum

def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := HasAxiomVerum.verum
@[simp] lemma verum! [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := ⟨verum⟩


class HasAxiomImply₁ (𝓢 : S)  where
  imply₁ {φ ψ : F} : 𝓢 ⊢! Axioms.Imply₁ φ ψ
export HasAxiomImply₁ (imply₁)

@[simp] lemma imply₁! [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ := ⟨imply₁⟩

def C_of_conseq [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := imply₁ ⨀ h
alias dhyp := C_of_conseq

lemma C!_of_conseq! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ➝ φ := ⟨C_of_conseq d.some⟩
alias dhyp! := C!_of_conseq!


class HasAxiomImply₂ (𝓢 : S)  where
  imply₂ {φ ψ χ : F} : 𝓢 ⊢! Axioms.Imply₂ φ ψ χ
export HasAxiomImply₂ (imply₂)

@[simp] lemma imply₂! [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ⟨imply₂⟩


class HasAxiomAndElim (𝓢 : S)  where
  and₁ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₁ φ ψ
  and₂ {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁ and₂)


@[simp] lemma and₁! [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ φ := ⟨and₁⟩

def K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! φ := and₁ ⨀ d
@[grind] lemma K!_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := ⟨K_left d.some⟩


@[simp] lemma and₂! [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := ⟨and₂⟩

def K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ := and₂ ⨀ d
@[grind] lemma K!_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := ⟨K_right d.some⟩


class HasAxiomAndInst (𝓢 : S) where
  and₃ {φ ψ : F} : 𝓢 ⊢! Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃)

@[simp] lemma and₃! [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := ⟨and₃⟩

def K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂: 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ := and₃ ⨀ d₁ ⨀ d₂
@[grind] lemma K!_intro  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂: 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := ⟨K_intro d₁.some d₂.some⟩


class HasAxiomOrInst (𝓢 : S) where
  or₁ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₁ φ ψ
  or₂ {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁ or₂)

@[simp] lemma or₁! [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ➝ φ ⋎ ψ := ⟨or₁⟩

def A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := or₁ ⨀ d
@[grind] lemma A!_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A_intro_left d.some⟩

@[simp] lemma or₂! [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := ⟨or₂⟩

def A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := or₂ ⨀ d
@[grind] lemma A!_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A_intro_right d.some⟩


class HasAxiomOrElim (𝓢 : S) where
  or₃ {φ ψ χ : F} : 𝓢 ⊢! Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃)

@[simp] lemma or₃! [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ) ➝ χ := ⟨or₃⟩

def left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ := or₃ ⨀ d₁ ⨀ d₂
alias CA_of_C_of_C := left_A_intro

lemma left_A!_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ := ⟨left_A_intro d₁.some d₂.some⟩
alias CA!_of_C!_of_C! := left_A!_intro

def of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ➝ χ) (d₂ : 𝓢 ⊢! ψ ➝ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ := or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias A_cases := of_C_of_C_of_A

lemma of_C!_of_C!_of_A! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ➝ χ) (d₂ : 𝓢 ⊢ ψ ➝ χ) (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ := ⟨of_C_of_C_of_A d₁.some d₂.some d₃.some⟩
alias A!_cases := of_C!_of_C!_of_A!


class HasAxiomEFQ (𝓢 : S) where
  efq {φ : F} : 𝓢 ⊢! Axioms.EFQ φ

export HasAxiomEFQ (efq)
@[simp] lemma efq! [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := ⟨efq⟩

def of_O [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := efq ⨀ b
@[grind] lemma of_O! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := ⟨of_O h.some⟩


class HasAxiomElimContra (𝓢 : S)  where
  elimContra {φ ψ : F} : 𝓢 ⊢! Axioms.ElimContra φ ψ
export HasAxiomElimContra (elimContra)

@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢ (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elimContra⟩


class HasAxiomDNE (𝓢 : S) where
  dne {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (dne)

@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ := ⟨dne⟩


class HasAxiomPeirce (𝓢 : S) where
  peirce {φ ψ : F} : 𝓢 ⊢! Axioms.Peirce φ ψ
export HasAxiomPeirce (peirce)

@[simp] lemma peirce! [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ ➝ ψ) ➝ φ) ➝ φ := ⟨peirce⟩


class HasAxiomWeakLEM (𝓢 : S) where
  wlem {φ : F} : 𝓢 ⊢! Axioms.WeakLEM φ
export HasAxiomWeakLEM (wlem)

@[simp] lemma wlem! [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢ ∼φ ⋎ ∼∼φ := ⟨wlem⟩


class HasAxiomDummett (𝓢 : S) where
  dummett {φ ψ : F} : 𝓢 ⊢! Axioms.Dummett φ ψ
export HasAxiomDummett (dummett)

@[simp] lemma dummett! [HasAxiomDummett 𝓢] : 𝓢 ⊢ Axioms.Dummett φ ψ := ⟨dummett⟩


class HasAxiomKrieselPutnam (𝓢 : S) where
  krieselputnam {φ ψ χ : F} : 𝓢 ⊢! Axioms.KrieselPutnam φ ψ χ
export HasAxiomKrieselPutnam (krieselputnam)

@[simp] lemma krieselputnam! [HasAxiomKrieselPutnam 𝓢] : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam⟩


class HasAxiomScott (𝓢 : S) where
  scott {φ : F} : 𝓢 ⊢! Axioms.Scott φ
export HasAxiomScott (scott)

@[simp] lemma scott! [HasAxiomScott 𝓢] : 𝓢 ⊢ ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ := ⟨scott⟩

/-
section

variable [HasAxiomKrieselPutnam 𝓢]

def krieselputnam : 𝓢 ⊢! (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := HasAxiomKrieselPutnam.krieselputnam φ ψ χ
@[simp] lemma krieselputnam! : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨fun _ _ _ ↦ FiniteContext.of krieselputnam⟩
instance (Γ : Context F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨fun _ _ _ ↦ Context.of krieselputnam⟩

def krieselputnam' (h : 𝓢 ⊢! (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢! (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := krieselputnam ⨀ h
lemma krieselputnam'! (h : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam' h.some⟩

end
-/

class HasAxiomScott (𝓢 : S) where
  scott (φ : F) : 𝓢 ⊢! Axioms.Scott φ

section

variable [HasAxiomScott 𝓢]

def scott : 𝓢 ⊢! ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ := HasAxiomScott.scott φ
@[simp] lemma scott! : 𝓢 ⊢ ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ := ⟨scott⟩

end


class HasAxiomPeirce (𝓢 : S) where
  peirce (φ ψ : F) : 𝓢 ⊢! Axioms.Peirce φ ψ

section

variable [HasAxiomPeirce 𝓢]

def peirce : 𝓢 ⊢! ((φ ➝ ψ) ➝ φ) ➝ φ := HasAxiomPeirce.peirce φ ψ
@[simp] lemma peirce! : 𝓢 ⊢ ((φ ➝ ψ) ➝ φ) ➝ φ := ⟨peirce⟩

end


section

variable (𝓢 : S)

protected class KC extends Entailment.Int 𝓢, HasAxiomWeakLEM 𝓢

protected class LC extends Entailment.Int 𝓢, HasAxiomDummett 𝓢

protected class KrieselPutnam extends Entailment.Int 𝓢, HasAxiomKrieselPutnam 𝓢

protected class Sc extends Entailment.Int 𝓢, HasAxiomScott 𝓢

end


end LO.Entailment
