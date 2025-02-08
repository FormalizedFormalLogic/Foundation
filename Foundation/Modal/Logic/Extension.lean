import Foundation.Modal.Logic.Basic

namespace LO.Modal

variable {L L₀ L₁ L₂ L₃ : Logic}

namespace Logic

inductive sumQuasiNormal (L₁ L₂ : Logic) : Logic
  | mem₁ {φ}    : φ ∈ L₁ → sumQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → sumQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ ➝ ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
  | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

inductive sumNormal (L₁ L₂ : Logic) : Logic
  | mem₁ {φ}    : φ ∈ L₁ → sumNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → sumNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumNormal L₁ L₂ (φ ➝ ψ) → sumNormal L₁ L₂ φ → sumNormal L₁ L₂ ψ
  | subst {φ s} : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (□φ)

end Logic


def QuasiNormalExtension (L : Logic) := { L' : Logic // L ⊆ L' ∧ L'.QuasiNormal }

namespace QuasiNormalExtension

variable {L₀ : Logic} {L : QuasiNormalExtension L₀}

instance : Membership (Formula ℕ) (QuasiNormalExtension L₀) := ⟨λ L φ => φ ∈ L.1⟩

lemma mem_of_mem_base (h : φ ∈ L₀) : φ ∈ L := L.property.1 h

lemma mem_of_mem_LogicK (h : φ ∈ Logic.K) : φ ∈ L := L.property.2.subset_K h

lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := L.property.2.mdp_closed hφψ hφ

lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := L.property.2.subst_closed hφ s

def add (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := Logic.sumQuasiNormal L₁.1 L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Logic.sumQuasiNormal.mem₁;
      apply mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Logic.sumQuasiNormal.mem₁;
        apply mem_of_mem_LogicK hφ;
      . intro φ ψ hφ hφψ;
        apply Logic.sumQuasiNormal.mdp hφ hφψ;
      . intro φ hφ s;
        apply Logic.sumQuasiNormal.subst hφ;

instance : Add (QuasiNormalExtension L₀) := ⟨add⟩

/-
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
-/

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


def ExtensionNormal (L : Logic) := { L' : Logic // L'.Normal ∧ L ⊆ L' }

namespace ExtensionNormal

end ExtensionNormal

end LO.Modal
