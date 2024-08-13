import Logic.Logic.HilbertStyle.Basic

namespace LO

section

class LukasiewiczAbbrev (F : Type*) [LogicalConnective F] where
  top : ⊤ = ~(⊥ : F)
  neg {p : F} : ~p = p ⟶ ⊥
  or {p q : F} : p ⋎ q = ~p ⟶ q
  and {p q : F} : p ⋏ q = ~(p ⟶ ~q)

attribute [simp]
  LukasiewiczAbbrev.top
  LukasiewiczAbbrev.neg
  LukasiewiczAbbrev.or
  LukasiewiczAbbrev.and

instance [LogicalConnective F] [LukasiewiczAbbrev F] : NegAbbrev F := ⟨LukasiewiczAbbrev.neg⟩

end


namespace System

variable {S F : Type*} [LogicalConnective F] [LukasiewiczAbbrev F] [System F S]

variable (𝓢 : S)

protected class Lukasiewicz [LukasiewiczAbbrev F]
  extends ModusPonens 𝓢,
          HasAxiomImply₁ 𝓢,
          HasAxiomImply₂ 𝓢,
          HasAxiomElimContra 𝓢

namespace Lukasiewicz

variable {𝓢 : S} {p p₁ p₂ q q₁ q₂ r s t : F}

variable [System.Lukasiewicz 𝓢]

def verum : 𝓢 ⊢ ⊤ := by simp [LukasiewiczAbbrev.top]; exact impId ⊥;
instance : HasAxiomVerum 𝓢 := ⟨Lukasiewicz.verum⟩

private def elim_contra₂ : 𝓢 ⊢ (~q ⟶ ~p) ⟶ (p ⟶ q) := by
  have : 𝓢 ⊢ ((q ⟶ ⊥) ⟶ (p ⟶ ⊥)) ⟶ (p ⟶ q) := elim_contra
  repeat rw [LukasiewiczAbbrev.neg];
  exact this;

def dne : 𝓢 ⊢ ~~p ⟶ p := by
  have d₁ : 𝓢 ⊢ ~~p ⟶ (~~(~~p) ⟶ ~~p) ⟶ ~p ⟶ ~(~~p) := dhyp _ $ elim_contra₂;
  have d₂ : 𝓢 ⊢ ~~p ⟶ ~~(~~p) ⟶ ~~p := imply₁;
  have d₃ : 𝓢 ⊢ ~~p ⟶ (~p ⟶ ~(~~p)) ⟶ ~~p ⟶ p := dhyp _ $ elim_contra₂;
  have d₄ : 𝓢 ⊢ ~~p ⟶ ~p ⟶ ~(~~p) := d₁ ⨀₁ d₂;
  have d₅ : 𝓢 ⊢ ~~p ⟶ ~~p ⟶ p := d₃ ⨀₁ d₄;
  have d₆ : 𝓢 ⊢ ~~p ⟶ ~~p := impId _;
  exact d₅ ⨀₁ d₆;
instance : HasAxiomDNE 𝓢 := ⟨λ p => Lukasiewicz.dne (p := p)⟩

def dni : 𝓢 ⊢ p ⟶ ~~p := by
  have d₁ : 𝓢 ⊢ (~(~~p) ⟶ ~p) ⟶ p ⟶ ~~p := elim_contra₂;
  have d₂ : 𝓢 ⊢ ~(~~p) ⟶ ~p := dne (p := ~p);
  exact d₁ ⨀ d₂;

def explode (h₁ : 𝓢 ⊢ p) (h₂ : 𝓢 ⊢ ~p) : 𝓢 ⊢ q := by
  have d₁ := imply₁ (𝓢 := 𝓢) (p := ~p) (q := ~q);
  have := d₁ ⨀ h₂;
  exact elim_contra₂ ⨀ this ⨀ h₁;

def explodeHyp (h₁ : 𝓢 ⊢ p ⟶ q) (h₂ : 𝓢 ⊢ p ⟶ ~q) : 𝓢 ⊢ p ⟶ r := by
  have : 𝓢 ⊢ p ⟶ ~q ⟶ ~(r) ⟶ ~q := dhyp imply₁ (q := p)
  have : 𝓢 ⊢ p ⟶ ~(r) ⟶ ~q := this ⨀₁ h₂;
  have : 𝓢 ⊢ p ⟶ q ⟶ r := (dhyp elim_contra₂ (q := p)) ⨀₁ this;
  exact this ⨀₁ h₁;

def explodeHyp₂ (h₁ : 𝓢 ⊢ p ⟶ q ⟶ r) (h₂ : 𝓢 ⊢ p ⟶ q ⟶ ~(r)) : 𝓢 ⊢ p ⟶ q ⟶ s := by
  have : 𝓢 ⊢ p ⟶ q ⟶ ~(r) ⟶ ~s ⟶ ~(r) := dhyp (dhyp imply₁ (q := q)) (q := p)
  have : 𝓢 ⊢ p ⟶ q ⟶ ~(s) ⟶ ~(r) := this ⨀₂ h₂;
  have : 𝓢 ⊢ p ⟶ q ⟶ r ⟶ s := (dhyp (dhyp elim_contra₂ (q := q)) (q := p)) ⨀₂ this;
  exact this ⨀₂ h₁;

def efq : 𝓢 ⊢ ⊥ ⟶ p := by
  have := explodeHyp (𝓢 := 𝓢) (p := ⊥) (q := ⊤) (r := p);
  exact this (by simp; exact imply₁) (by simp; exact imply₁);
instance : HasAxiomEFQ 𝓢 := ⟨λ p => Lukasiewicz.efq (p := p)⟩

def impSwap (h : 𝓢 ⊢ p ⟶ q ⟶ r) : 𝓢 ⊢ q ⟶ p ⟶ r := by
  refine mdp₂ (r := q) ?_ ?_;
  . exact dhyp q h;
  . exact imply₁;

def mdpIn₁ : 𝓢 ⊢ (p ⟶ q) ⟶ p ⟶ q := impId _

def mdpIn₂ : 𝓢 ⊢ p ⟶ (p ⟶ q) ⟶ q := impSwap mdpIn₁

def mdp₂In₁ : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r) := imply₂

def mdp₂In₂ : 𝓢 ⊢ (p ⟶ q) ⟶ (p ⟶ q ⟶ r) ⟶ (p ⟶ r) := impSwap mdp₂In₁

def impTrans'₁ (bpq : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ (q ⟶ r) ⟶ (p ⟶ r) := by
  apply impSwap;
  exact impTrans'' bpq mdpIn₂;

def impTrans'₂ (bqr: 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ (p ⟶ q) ⟶ (p ⟶ r) := imply₂ ⨀ (dhyp p bqr)

def impTrans₂ : 𝓢 ⊢ (q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r) := impTrans'' (impSwap (dhyp p (impId (q ⟶ r)))) mdp₂In₁

def impTrans₁ : 𝓢 ⊢ (p ⟶ q) ⟶ (q ⟶ r) ⟶ (p ⟶ r) := impSwap impTrans₂

def dhypBoth (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ (p ⟶ q) ⟶ (p ⟶ r) := imply₂ ⨀ (dhyp _ $ h)

def explode₂₁ : 𝓢 ⊢ ~p ⟶ p ⟶ q := by
  simp;
  exact dhypBoth efq;

def explode₁₂ : 𝓢 ⊢ p ⟶ ~p ⟶ q := impSwap explode₂₁

def contraIntro : 𝓢 ⊢ (p ⟶ q) ⟶ (~q ⟶ ~p):= by simpa using impTrans₁;

def contraIntro' : 𝓢 ⊢ (p ⟶ q) → 𝓢 ⊢ (~q ⟶ ~p) := λ h => contraIntro ⨀ h

def andElim₁ : 𝓢 ⊢ p ⋏ q ⟶ p := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ ~p ⟶ p ⟶ ~q := explodeHyp₂ explode₂₁ imply₁;
  have : 𝓢 ⊢ ~(p ⟶ ~q) ⟶ ~~p := contraIntro' explode₂₁
  exact impTrans'' this dne;
instance : HasAxiomAndElim₁ 𝓢 := ⟨λ p q => Lukasiewicz.andElim₁ (p := p) (q := q)⟩

def andElim₂ : 𝓢 ⊢ p ⋏ q ⟶ q := by
  simp only [LukasiewiczAbbrev.and];
  have := imply₁ (𝓢 := 𝓢) (p := ~q) (q := p);
  have := contraIntro' this;
  exact impTrans'' this dne;
instance : HasAxiomAndElim₂ 𝓢 := ⟨λ p q => Lukasiewicz.andElim₂ (p := p) (q := q)⟩

def andImplyLeft : 𝓢 ⊢ (p₁ ⟶ q) ⟶ p₁ ⋏ p₂ ⟶ q := (impSwap $ dhyp _ (impId _)) ⨀₂ (dhyp _ andElim₁)
def andImplyLeft' (h : 𝓢 ⊢ (p₁ ⟶ q)) : 𝓢 ⊢ p₁ ⋏ p₂ ⟶ q := andImplyLeft ⨀ h

def andImplyRight : 𝓢 ⊢ (p₂ ⟶ q) ⟶ p₁ ⋏ p₂ ⟶ q := (impSwap $ dhyp _ (impId _)) ⨀₂ (dhyp _ andElim₂)
def andImplyRight' (h : 𝓢 ⊢ (p₂ ⟶ q)) : 𝓢 ⊢ p₁ ⋏ p₂ ⟶ q := andImplyRight ⨀ h

def andInst'' (hp : 𝓢 ⊢ p) (hq : 𝓢 ⊢ q) : 𝓢 ⊢ p ⋏ q := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ (p ⟶ ~q) ⟶ p ⟶ ~q := impId _
  have : 𝓢 ⊢ (p ⟶ ~q) ⟶ ~q := this ⨀₁ dhyp _ hp;
  have : 𝓢 ⊢ q ⟶ ~(p ⟶ ~q) := impTrans'' dni $ contraIntro' this;
  exact this ⨀ hq;

-- and_destruct
def andInst : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q := by
  sorry;

instance : HasAxiomAndInst 𝓢 := ⟨λ p q => Lukasiewicz.andInst (p := p) (q := q)⟩

def orInst₁ : 𝓢 ⊢ p ⟶ p ⋎ q := by
  simp only [LukasiewiczAbbrev.or];
  exact explode₁₂;

instance : HasAxiomOrInst₁ 𝓢 := ⟨λ p q => Lukasiewicz.orInst₁ (p := p) (q := q)⟩

def orInst₂ : 𝓢 ⊢ q ⟶ p ⋎ q := by
  simp [LukasiewiczAbbrev.or];
  exact imply₁;
instance : HasAxiomOrInst₂ 𝓢 := ⟨λ p q => Lukasiewicz.orInst₂ (p := p) (q := q)⟩

-- or_imply
def orElim : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp only [LukasiewiczAbbrev.or];
  sorry;

instance : HasAxiomOrElim 𝓢 := ⟨λ p q r => Lukasiewicz.orElim (p := p) (q := q) (r := r)⟩

instance : System.Classical 𝓢 where

end Lukasiewicz

end System

end LO
