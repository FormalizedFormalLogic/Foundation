import Foundation.Modal.Formula

namespace LO.Modal

variable {α : Type u}

inductive NNFormula (α : Type u) : Type u where
  | atom   : α → NNFormula α
  | natom  : α → NNFormula α
  | falsum : NNFormula α
  | verum  : NNFormula α
  | or     : NNFormula α → NNFormula α → NNFormula α
  | and    : NNFormula α → NNFormula α → NNFormula α
  | box    : NNFormula α → NNFormula α
  | dia    : NNFormula α → NNFormula α
  deriving DecidableEq

namespace NNFormula

variable {φ ψ χ : NNFormula α}

def neg : NNFormula α → NNFormula α
  | atom a  => natom a
  | natom a => atom a
  | falsum  => verum
  | verum   => falsum
  | or φ ψ  => and (neg φ) (neg ψ)
  | and φ ψ => or (neg φ) (neg ψ)
  | box φ   => dia (neg φ)
  | dia φ   => box (neg φ)

abbrev imp (φ ψ : NNFormula α) : NNFormula α := or (neg φ) ψ

instance : BasicModalLogicalConnective (NNFormula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

lemma or_eq : or φ ψ = φ ⋎ ψ := rfl

lemma and_eq : and φ ψ = φ ⋏ ψ := rfl

lemma imp_eq : imp φ ψ = φ ➝ ψ := rfl

lemma neg_eq : neg φ = ∼φ := rfl

lemma box_eq : box φ = □φ := rfl

lemma dia_eq : dia φ = ◇φ := rfl

lemma iff_eq : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl

lemma falsum_eq : (falsum : NNFormula α) = ⊥ := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

end NNFormula


end LO.Modal
