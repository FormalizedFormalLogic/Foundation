module
import Foundation.Propositional.Formula
import Foundation.Propositional.NNFormula

namespace LO.Propositional

def Formula.toNNFormula : Formula α → NNFormula α
  | .atom a => .atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.toNNFormula) ➝ (ψ.toNNFormula)
  | φ ⋏ ψ => (φ.toNNFormula) ⋏ (ψ.toNNFormula)
  | φ ⋎ ψ => (φ.toNNFormula) ⋎ (ψ.toNNFormula)

namespace Formula.toNNFormula

local postfix:80 "ᵗ" => toNNFormula

instance : Coe (Formula α) (NNFormula α) := ⟨Formula.toNNFormula⟩

@[simp] lemma def_bot : (⊥ : Formula α)ᵗ = ⊥ := by rfl

@[simp] lemma def_atom : (.atom a)ᵗ = .atom a := by rfl

@[simp] lemma def_imp : (φ ➝ ψ)ᵗ = φᵗ ➝ ψᵗ := by rfl

@[simp] lemma def_and : (φ ⋏ ψ)ᵗ = φᵗ ⋏ ψᵗ := by rfl

@[simp] lemma def_or : (φ ⋎ ψ)ᵗ = φᵗ ⋎ ψᵗ := by rfl

end Formula.toNNFormula


def NNFormula.toFormula : NNFormula α → Formula α
  | .atom a => .atom a
  | .natom a => ∼(.atom a)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => (φ.toFormula) ⋏ (ψ.toFormula)
  | φ ⋎ ψ => (φ.toFormula) ⋎ (ψ.toFormula)

namespace NNFormula.toFormula

local postfix:80 "ᵗ" => toFormula

instance : Coe (NNFormula α) (Formula α) := ⟨NNFormula.toFormula⟩

@[simp] lemma def_top : (⊤ : NNFormula α)ᵗ = ⊤ := by rfl

@[simp] lemma def_bot : (⊥ : NNFormula α)ᵗ = ⊥ := by rfl

@[simp] lemma def_atom : (.atom a)ᵗ = (.atom a) := by rfl

@[simp] lemma def_natom : (.natom a)ᵗ = ∼(.atom a) := by rfl

@[simp] lemma def_and : (φ ⋏ ψ)ᵗ = φᵗ ⋏ ψᵗ := by rfl

@[simp] lemma def_or : (φ ⋎ ψ)ᵗ = φᵗ ⋎ ψᵗ := by rfl

end NNFormula.toFormula

end LO.Propositional
