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

variable [System.Lukasiewicz 𝓢]

def verum : 𝓢 ⊢ ⊤ := by simp [LukasiewiczAbbrev.top]; exact impId ⊥;
instance : HasAxiomVerum 𝓢 := ⟨Lukasiewicz.verum (𝓢 := 𝓢)⟩

variable {p q r : F}

attribute [local simp]
  HasAxiomImply₁.imply₁
  HasAxiomImply₂.imply₂

def orInst₁ : 𝓢 ⊢ p ⟶ p ⋎ q := by
  simp [LukasiewiczAbbrev.or];
  sorry;

instance : HasAxiomOrInst₁ 𝓢 := ⟨λ p q => Lukasiewicz.orInst₁ (𝓢 := 𝓢) (p := p) (q := q)⟩

def orInst₂ : 𝓢 ⊢ q ⟶ p ⋎ q := by
  simp [LukasiewiczAbbrev.or];
  exact imply₁;
instance : HasAxiomOrInst₂ 𝓢 := ⟨λ p q => Lukasiewicz.orInst₂ (𝓢 := 𝓢) (p := p) (q := q)⟩

def orElim : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp only [LukasiewiczAbbrev.or];
  sorry;
instance : HasAxiomOrElim 𝓢 := ⟨λ p q r => Lukasiewicz.orElim (𝓢 := 𝓢) (p := p) (q := q) (r := r)⟩

def andInst : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q := by
  simp only [LukasiewiczAbbrev.and];
  sorry;
instance : HasAxiomAndInst 𝓢 := ⟨λ p q => Lukasiewicz.andInst (𝓢 := 𝓢) (p := p) (q := q)⟩

def andElim₁ : 𝓢 ⊢ p ⋏ q ⟶ p := by
  simp only [LukasiewiczAbbrev.and];
  refine imply₂ (𝓢 := 𝓢) (p := ~(p ⟶ ~q)) (q := p) (r := p) ⨀ ?_ ⨀ ?_;
  . sorry;
  . sorry;
instance : HasAxiomAndElim₁ 𝓢 := ⟨λ p q => Lukasiewicz.andElim₁ (𝓢 := 𝓢) (p := p) (q := q)⟩

def andElim₂ : 𝓢 ⊢ p ⋏ q ⟶ q := by
  simp only [LukasiewiczAbbrev.and];
  sorry;
instance : HasAxiomAndElim₂ 𝓢 := ⟨λ p q => Lukasiewicz.andElim₂ (𝓢 := 𝓢) (p := p) (q := q)⟩

def dne : 𝓢 ⊢ ~(~p) ⟶ p := by
  sorry;
instance : HasAxiomDNE 𝓢 := ⟨λ p => Lukasiewicz.dne (𝓢 := 𝓢) (p := p)⟩

instance : System.Classical 𝓢 where

end Lukasiewicz

end System

end LO
