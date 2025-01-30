import Foundation.Modal.Formula
import Foundation.Modal.Substitution
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Hilbert.K

namespace LO.Modal

variable {L L₁ L₂ L₃ : Logic α}

namespace Logic

class QuasiNormal (L : Logic α) where
  subset_K : Logic.K α ⊆ L
  mdp_closed {φ ψ} : (φ ➝ ψ) ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → (∀ s, φ⟦s⟧ ∈ L)

class Normal (L : Logic α) extends QuasiNormal L where
  nec_closed {φ} : φ ∈ L → □φ ∈ L


inductive closureQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : φ ∈ L₁ → closureQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → closureQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : closureQuasiNormal L₁ L₂ (φ ➝ ψ) → closureQuasiNormal L₁ L₂ φ → closureQuasiNormal L₁ L₂ ψ
  | subst {φ s} : closureQuasiNormal L₁ L₂ φ → closureQuasiNormal L₁ L₂ (φ⟦s⟧)
-- infix:80 " +ᴸ " => sumQuasiNormal

-- def addQuasiNormal (L₁ : Logic α) (φ : Formula α) : Logic α := L₁ +ᴸ {φ}
-- infix:80 " +ᴸ " => addQuasiNormal

inductive closureNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : φ ∈ L₁ → closureNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → closureNormal L₁ L₂ φ
  | mdp  {φ ψ}  : closureNormal L₁ L₂ (φ ➝ ψ) → closureNormal L₁ L₂ φ → closureNormal L₁ L₂ ψ
  | subst {φ s} : closureNormal L₁ L₂ φ → closureNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : closureNormal L₁ L₂ φ → closureNormal L₁ L₂ (□φ)
-- infix:80 " ⊕ᴸ " => sumNormal

-- def addNormal (L₁ : Logic α) (φ : Formula α) : Logic α := L₁ ⊕ᴸ {φ}
-- infix:80 " ⊕ᴸ " => addNormal


end Logic


def QuasiNormalExtension (L : Logic α) := { L' : Logic α // L ⊆ L' ∧ L'.QuasiNormal }

namespace QuasiNormalExtension

variable {L₀ : Logic α} {L : QuasiNormalExtension L₀}

instance : Membership (Formula α) (QuasiNormalExtension L₀) := ⟨λ L φ => φ ∈ L.1⟩

lemma mem_of_mem_base (h : φ ∈ L₀) : φ ∈ L := L.property.1 h

lemma mem_of_mem_LogicK (h : φ ∈ Logic.K _) : φ ∈ L := L.property.2.1 h

lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := L.property.2.2 hφψ hφ

lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := L.property.2.3 hφ s

def add (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := Logic.closureQuasiNormal L₁.1 L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Logic.closureQuasiNormal.mem₁;
      apply mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Logic.closureQuasiNormal.mem₁;
        apply mem_of_mem_LogicK hφ;
      . intro φ ψ hφ hφψ;
        apply Logic.closureQuasiNormal.mdp hφ hφψ;
      . intro φ hφ s;
        apply Logic.closureQuasiNormal.subst hφ;

instance : Add (QuasiNormalExtension L₀) := ⟨add⟩

instance : Std.IdempotentOp (α := QuasiNormalExtension L₀) (· + ·) where
  idempotent := by
    intro L;
    sorry;

instance : Std.Commutative (α := QuasiNormalExtension L₀) (· + ·) where
  comm := by
    intro L₁ L₂;
    sorry;

instance : Std.Associative (α := QuasiNormalExtension L₀) (· + ·) where
  assoc := by
    intro L₁ L₂ L₃;
    sorry;

def inter (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := L₁.1 ∩ L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Set.mem_inter <;> exact mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Set.mem_inter <;> exact mem_of_mem_LogicK hφ;
      . rintro φ ψ ⟨hφψ₁, hφψ₂⟩ ⟨hφ₁, hφ₂⟩;
        apply Set.mem_inter;
        . exact mdp hφψ₁ hφ₁;
        . exact mdp hφψ₂ hφ₂;
      . rintro φ ⟨hφ₁, hφ₂⟩ s;
        apply Set.mem_inter;
        . exact subst hφ₁;
        . exact subst hφ₂;

instance : Inter (QuasiNormalExtension L₀) := ⟨inter⟩

end QuasiNormalExtension


def ExtensionNormal (L : Logic α) := { L' : Logic α // L'.Normal ∧ L ⊆ L' }

namespace ExtensionNormal

end ExtensionNormal


instance : (Logic.K α).Normal where
  subset_K := by tauto;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    sorry;
  nec_closed := by
    intro φ hφ;
    exact System.nec! hφ;

end LO.Modal
