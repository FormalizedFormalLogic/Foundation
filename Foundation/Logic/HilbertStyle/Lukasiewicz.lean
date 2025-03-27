import Foundation.Logic.HilbertStyle.Basic

namespace LO

section

class LukasiewiczAbbrev (F : Type*) [LogicalConnective F] where
  top : ⊤ = ∼(⊥ : F)
  neg {φ : F} : ∼φ = φ ➝ ⊥
  or {φ ψ : F} : φ ⋎ ψ = ∼φ ➝ ψ
  and {φ ψ : F} : φ ⋏ ψ = ∼(φ ➝ ∼ψ)

instance [LogicalConnective F] [LukasiewiczAbbrev F] : NegAbbrev F := ⟨LukasiewiczAbbrev.neg⟩

end


namespace Entailment

attribute [local simp]
  LukasiewiczAbbrev.top
  LukasiewiczAbbrev.neg
  LukasiewiczAbbrev.or
  LukasiewiczAbbrev.and

variable {S F : Type*} [LogicalConnective F] [LukasiewiczAbbrev F] [Entailment F S]

variable (𝓢 : S)

protected class Lukasiewicz [LukasiewiczAbbrev F]
  extends ModusPonens 𝓢,
          HasAxiomImply₁ 𝓢,
          HasAxiomImply₂ 𝓢,
          HasAxiomElimContra 𝓢

namespace Lukasiewicz

variable {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ s t : F}

variable [Entailment.Lukasiewicz 𝓢]

def verum : 𝓢 ⊢ ⊤ := by simp [LukasiewiczAbbrev.top]; exact cId ⊥;
instance : HasAxiomVerum 𝓢 := ⟨Lukasiewicz.verum⟩

def dne : 𝓢 ⊢ ∼∼φ ➝ φ := by
  have d₁ : 𝓢 ⊢ ∼∼φ ➝ (∼∼(∼∼φ) ➝ ∼∼φ) ➝ ∼φ ➝ ∼(∼∼φ) := cψφOfφ $ elimContra;
  have d₂ : 𝓢 ⊢ ∼∼φ ➝ ∼∼(∼∼φ) ➝ ∼∼φ := imply₁;
  have d₃ : 𝓢 ⊢ ∼∼φ ➝ (∼φ ➝ ∼(∼∼φ)) ➝ ∼∼φ ➝ φ := cψφOfφ $ elimContra;
  have d₄ : 𝓢 ⊢ ∼∼φ ➝ ∼φ ➝ ∼(∼∼φ) := d₁ ⨀₁ d₂;
  have d₅ : 𝓢 ⊢ ∼∼φ ➝ ∼∼φ ➝ φ := d₃ ⨀₁ d₄;
  have d₆ : 𝓢 ⊢ ∼∼φ ➝ ∼∼φ := cId _;
  exact d₅ ⨀₁ d₆;
instance : HasAxiomDNE 𝓢 := ⟨λ φ => Lukasiewicz.dne (φ := φ)⟩

def dni : 𝓢 ⊢ φ ➝ ∼∼φ := by
  have d₁ : 𝓢 ⊢ (∼(∼∼φ) ➝ ∼φ) ➝ φ ➝ ∼∼φ := elimContra;
  have d₂ : 𝓢 ⊢ ∼(∼∼φ) ➝ ∼φ := dne (φ := ∼φ);
  exact d₁ ⨀ d₂;

def explode (h₁ : 𝓢 ⊢ φ) (h₂ : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := by
  have d₁ := imply₁ (𝓢 := 𝓢) (φ := ∼φ) (ψ := ∼ψ);
  have := d₁ ⨀ h₂;
  exact elimContra ⨀ this ⨀ h₁;

def explodeHyp (h₁ : 𝓢 ⊢ φ ➝ ψ) (h₂ : 𝓢 ⊢ φ ➝ ∼ψ) : 𝓢 ⊢ φ ➝ χ := by
  have : 𝓢 ⊢ φ ➝ ∼ψ ➝ ∼χ ➝ ∼ψ := cψφOfφ imply₁ (ψ := φ)
  have : 𝓢 ⊢ φ ➝ ∼χ ➝ ∼ψ := this ⨀₁ h₂;
  have : 𝓢 ⊢ φ ➝ ψ ➝ χ := (cψφOfφ elimContra (ψ := φ)) ⨀₁ this;
  exact this ⨀₁ h₁;

def explodeHyp₂ (h₁ : 𝓢 ⊢ φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢ φ ➝ ψ ➝ ∼χ) : 𝓢 ⊢ φ ➝ ψ ➝ s := by
  have : 𝓢 ⊢ φ ➝ ψ ➝ ∼χ ➝ ∼s ➝ ∼χ := cψφOfφ (cψφOfφ imply₁ (ψ := ψ)) (ψ := φ)
  have : 𝓢 ⊢ φ ➝ ψ ➝ ∼(s) ➝ ∼χ := this ⨀₂ h₂;
  have : 𝓢 ⊢ φ ➝ ψ ➝ χ ➝ s := (cψφOfφ (cψφOfφ elimContra (ψ := ψ)) (ψ := φ)) ⨀₂ this;
  exact this ⨀₂ h₁;

def efq : 𝓢 ⊢ ⊥ ➝ φ := by
  have := explodeHyp (𝓢 := 𝓢) (φ := ⊥) (ψ := ⊤) (χ := φ);
  exact this (by simp; exact imply₁) (by simp; exact imply₁);
instance : HasAxiomEFQ 𝓢 := ⟨λ φ => Lukasiewicz.efq (φ := φ)⟩

def impSwap (h : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ φ ➝ χ := by
  refine mdp₂ (χ := ψ) ?_ ?_;
  . exact cψφOfφ h;
  . exact imply₁;

def mdpIn₁ : 𝓢 ⊢ (φ ➝ ψ) ➝ φ ➝ ψ := cId _

def mdpIn₂ : 𝓢 ⊢ φ ➝ (φ ➝ ψ) ➝ ψ := impSwap mdpIn₁

def mdp₂In₁ : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ (φ ➝ χ) := imply₂

def mdp₂In₂ : 𝓢 ⊢ (φ ➝ ψ) ➝ (φ ➝ ψ ➝ χ) ➝ (φ ➝ χ) := impSwap mdp₂In₁

def cTrans'₁ (bpq : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (ψ ➝ χ) ➝ (φ ➝ χ) := by
  apply impSwap;
  exact cTrans bpq mdpIn₂;

def cTrans'₂ (bqr: 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ (φ ➝ ψ) ➝ (φ ➝ χ) := imply₂ ⨀ (cψφOfφ bqr)

def cTrans₂ : 𝓢 ⊢ (ψ ➝ χ) ➝ (φ ➝ ψ) ➝ (φ ➝ χ) := cTrans (impSwap (cψφOfφ (cId (ψ ➝ χ)))) mdp₂In₁

def cTrans₁ : 𝓢 ⊢ (φ ➝ ψ) ➝ (ψ ➝ χ) ➝ (φ ➝ χ) := impSwap cTrans₂

def dhypBoth (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ (φ ➝ ψ) ➝ (φ ➝ χ) := imply₂ ⨀ (cψφOfφ $ h)

def explode₂₁ : 𝓢 ⊢ ∼φ ➝ φ ➝ ψ := by
  simp;
  exact dhypBoth efq;

def explode₁₂ : 𝓢 ⊢ φ ➝ ∼φ ➝ ψ := impSwap explode₂₁

def contraIntro : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ):= by simpa using cTrans₁;

def contraIntro' : 𝓢 ⊢ (φ ➝ ψ) → 𝓢 ⊢ (∼ψ ➝ ∼φ) := λ h => contraIntro ⨀ h

def andElim₁ : 𝓢 ⊢ φ ⋏ ψ ➝ φ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ ∼φ ➝ φ ➝ ∼ψ := explodeHyp₂ explode₂₁ imply₁;
  have : 𝓢 ⊢ ∼(φ ➝ ∼ψ) ➝ ∼∼φ := contraIntro' explode₂₁
  exact cTrans this dne;

def andElim₂ : 𝓢 ⊢ φ ⋏ ψ ➝ ψ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ ∼ψ ➝ φ ➝ ∼ψ := imply₁ (φ := ∼ψ) (ψ := φ);
  have : 𝓢 ⊢ ∼(φ ➝ ∼ψ) ➝ ∼∼ψ := contraIntro' this;
  exact cTrans this dne;
instance : HasAxiomAndElim 𝓢 := ⟨λ φ ψ => Lukasiewicz.andElim₁ (φ := φ) (ψ := ψ), λ φ ψ => Lukasiewicz.andElim₂ (φ := φ) (ψ := ψ)⟩

def andImplyLeft : 𝓢 ⊢ (φ₁ ➝ ψ) ➝ φ₁ ⋏ φ₂ ➝ ψ := (impSwap $ cψφOfφ (cId _)) ⨀₂ (cψφOfφ andElim₁)
def andImplyLeft' (h : 𝓢 ⊢ (φ₁ ➝ ψ)) : 𝓢 ⊢ φ₁ ⋏ φ₂ ➝ ψ := andImplyLeft ⨀ h

def andImplyRight : 𝓢 ⊢ (φ₂ ➝ ψ) ➝ φ₁ ⋏ φ₂ ➝ ψ := (impSwap $ cψφOfφ (cId _)) ⨀₂ (cψφOfφ andElim₂)
def andImplyRight' (h : 𝓢 ⊢ (φ₂ ➝ ψ)) : 𝓢 ⊢ φ₁ ⋏ φ₂ ➝ ψ := andImplyRight ⨀ h

def andInst'' (hp : 𝓢 ⊢ φ) (hq : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ φ ➝ ∼ψ := cId _
  have : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ ∼ψ := this ⨀₁ cψφOfφ hp;
  have : 𝓢 ⊢ ψ ➝ ∼(φ ➝ ∼ψ) := cTrans dni $ contraIntro' this;
  exact this ⨀ hq;

def andInst : 𝓢 ⊢ φ ➝ ψ ➝ φ ⋏ ψ := by
  have d₁ : 𝓢 ⊢ φ ➝ ψ ➝ (φ ➝ ∼ψ) ➝ φ ➝ ∼ψ := cψφOfφ <| cψφOfφ <| cId (φ ➝ ∼ψ);
  have d₂ : 𝓢 ⊢ φ ➝ ψ ➝ (φ ➝ ∼ψ) ➝ φ := cφcψcχcφ (φ := φ) (ψ := ψ) (χ := (φ ➝ ∼ψ));
  have d₃ : 𝓢 ⊢ φ ➝ ψ ➝ (φ ➝ ∼ψ) ➝ ψ := cψφOfφ <| imply₁;
  have d₄ : 𝓢 ⊢ φ ➝ ψ ➝ (φ ➝ ∼ψ) ➝ ∼ψ := d₁ ⨀₃ d₂;
  have d₄ : 𝓢 ⊢ φ ➝ ψ ➝ (φ ➝ ∼ψ) ➝ ψ ➝ ⊥ := by simpa using d₄;
  simpa using d₄ ⨀₃ d₃;

instance : HasAxiomAndInst 𝓢 := ⟨λ φ ψ => Lukasiewicz.andInst (φ := φ) (ψ := ψ)⟩


def orInst₁ : 𝓢 ⊢ φ ➝ φ ⋎ ψ := by
  simp only [LukasiewiczAbbrev.or];
  exact explode₁₂;

def orInst₂ : 𝓢 ⊢ ψ ➝ φ ⋎ ψ := by
  simp [LukasiewiczAbbrev.or];
  exact imply₁;

instance : HasAxiomOrInst 𝓢 := ⟨λ φ ψ => Lukasiewicz.orInst₁ (φ := φ) (ψ := ψ), λ φ ψ => Lukasiewicz.orInst₂ (φ := φ) (ψ := ψ)⟩

-- or_imply
def orElim : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  simp only [LukasiewiczAbbrev.or];
  have d₁ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ (φ ➝ χ) ➝ ∼χ ➝ ∼φ
    := (cψφOfφ (ψ := φ ➝ χ) <| cψφOfφ (ψ := ψ ➝ χ) <| cψφOfφ (ψ := ∼φ ➝ ψ) <| contraIntro (φ := φ) (ψ := χ));
  have d₂ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼χ ➝ ∼φ
    := d₁ ⨀₃ (cφcψcχcφ (φ ➝ χ) (ψ ➝ χ) (∼φ ➝ ψ));
  have d₃ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼χ ➝ ψ
    := (cψφOfφ (ψ := φ ➝ χ) <| cψφOfφ (ψ := ψ ➝ χ) <| imply₁ (φ := ∼φ ➝ ψ) (ψ := ∼χ)) ⨀₄ d₂;
  have d₄ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼χ ➝ χ
    := (cψφOfφ (ψ := φ ➝ χ) <| cφcψcχcφ (φ := ψ ➝ χ) (ψ := ∼φ ➝ ψ) (χ := ∼χ)) ⨀₄ d₃;
  have d₅ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼χ ➝ χ ➝ ⊥
    := by simpa using cψφOfφ (ψ := φ ➝ χ) <| cψφOfφ (ψ := ψ ➝ χ) <| cψφOfφ (ψ := ∼φ ➝ ψ) <| cId (φ := ∼χ);
  have d₆ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼∼χ
    := by simpa using d₅ ⨀₄ d₄;
  have d₇ : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (∼φ ➝ ψ) ➝ ∼∼χ ➝ χ
    := cψφOfφ (ψ := φ ➝ χ) <| cψφOfφ (ψ := ψ ➝ χ) <| cψφOfφ (ψ := ∼φ ➝ ψ) <| dne (φ := χ);
  exact d₇ ⨀₃ d₆;

instance : HasAxiomOrElim 𝓢 := ⟨λ φ ψ χ => Lukasiewicz.orElim (φ := φ) (ψ := ψ) (χ := χ)⟩

instance : Entailment.Classical 𝓢 where

end Lukasiewicz

end Entailment

end LO
