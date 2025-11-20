import Foundation.Propositional.Entailment.Minimal.Basic

namespace LO.Propositional

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}


namespace Axioms

variable (φ ψ χ)

protected abbrev DistributeAndOr := (φ ⋏ (ψ ⋎ χ)) ➝ ((φ ⋏ ψ) ⋎ (φ ⋏ χ))

protected abbrev C := (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ (ψ ⋏ χ))

protected abbrev D := (φ ➝ χ) ⋏ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

protected abbrev I := (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ χ)

protected abbrev ImpId := φ ➝ φ

end Axioms


namespace Entailment


class AFortiori (𝓢 : S) where
  af! {φ ψ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! ψ ➝ φ
export AFortiori (af!)

@[grind ←] lemma af [AFortiori 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ ➝ φ := λ ⟨h⟩ => ⟨af! h⟩


class AndIntroRule (𝓢 : S) where
  andIR! {φ ψ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! ψ → 𝓢 ⊢! φ ⋏ ψ
export AndIntroRule (andIR!)

@[grind ←] lemma andIR [AndIntroRule 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ → 𝓢 ⊢ φ ⋏ ψ := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨andIR! h₁ h₂⟩


class HasDistributeAndOr (𝓢 : S) where
  distributeAndOr! {φ ψ χ : F} : 𝓢 ⊢! Axioms.DistributeAndOr φ ψ χ
export HasDistributeAndOr (distributeAndOr!)

@[simp, grind .] lemma distributeAndOr [HasDistributeAndOr 𝓢] : 𝓢 ⊢ Axioms.DistributeAndOr φ ψ χ := ⟨distributeAndOr!⟩


class HasAxiomC (𝓢 : S) where
  axiomC! {φ ψ χ : F} : 𝓢 ⊢! Axioms.C φ ψ χ
export HasAxiomC (axiomC!)

@[simp, grind .] lemma axiomC [HasAxiomC 𝓢] : 𝓢 ⊢ Axioms.C φ ψ χ := ⟨axiomC!⟩

class HasAxiomD (𝓢 : S) where
  axiomD! {φ ψ χ : F} : 𝓢 ⊢! Axioms.D φ ψ χ
export HasAxiomD (axiomD!)

@[simp, grind .] lemma axiomD [HasAxiomD 𝓢] : 𝓢 ⊢ Axioms.D φ ψ χ := ⟨axiomD!⟩


class HasAxiomI (𝓢 : S) where
  axiomI! {φ ψ χ : F} : 𝓢 ⊢! Axioms.I φ ψ χ
export HasAxiomI (axiomI!)

@[simp, grind .] lemma axiomI [HasAxiomI 𝓢] : 𝓢 ⊢ Axioms.I φ ψ χ := ⟨axiomI!⟩


class HasImpId (𝓢 : S) where
  impId! {φ : F} : 𝓢 ⊢! Axioms.ImpId φ
export HasImpId (impId!)

@[simp, grind .] lemma impId [HasImpId 𝓢] : 𝓢 ⊢ Axioms.ImpId φ := ⟨impId!⟩


end Entailment

end LO.Propositional
