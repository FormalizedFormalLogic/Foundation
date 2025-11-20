import Foundation.Propositional.Entailment.Minimal.Basic

namespace LO.Propositional

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ ξ : F}


namespace Axioms

variable (φ ψ χ ξ)

protected abbrev DistributeAndOr := (φ ⋏ (ψ ⋎ χ)) ➝ ((φ ⋏ ψ) ⋎ (φ ⋏ χ))

protected abbrev C := (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ (ψ ⋏ χ))

protected abbrev D := (φ ➝ χ) ⋏ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

protected abbrev I := (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ χ)

protected abbrev ImpId := φ ➝ φ


/-- Axiom of reflexivity for Kripke frame -/
protected abbrev Rfl := (φ ⋏ (φ ➝ ψ)) ➝ ψ

/-- Axioms of coreflexivity for Kripke frame -/
protected abbrev Corefl := (φ ➝ ψ ➝ φ) ⋏ (φ ⋎ ∼φ)


/-- Axiom 1 of transitivity for Kripke frame -/
protected abbrev Tra1 := (φ ➝ ψ) ➝ (χ ➝ φ ➝ ψ)

/-- Axiom 2 of transitivity for Kripke frame -/
protected abbrev Tra2 := (φ ➝ ψ) ➝ (ψ ➝ χ) ➝ (φ ➝ χ)


/-- Axioms of symmetry for Kripke frame -/
protected abbrev Sym := φ ➝ (ψ ⋎ ∼(φ ➝ ψ))


/-- Axioms of seriality for Kripke frame -/
protected abbrev Ser : F := ∼∼⊤


/-- Axioms of persistency for Kripke frame -/
protected abbrev Per := φ ➝ ⊤ ➝ φ

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


class HasAxiomRfl (𝓢 : S) where
  axiomRfl! {φ ψ : F} : 𝓢 ⊢! Axioms.Rfl φ ψ
export HasAxiomRfl (axiomRfl!)
@[simp, grind .] lemma axiomRfl [HasAxiomRfl 𝓢] : 𝓢 ⊢ Axioms.Rfl φ ψ := ⟨axiomRfl!⟩


class HasAxiomCorfl (𝓢 : S) where
  axiomCorfl! {φ ψ : F} : 𝓢 ⊢! Axioms.Corefl φ ψ
export HasAxiomCorfl (axiomCorfl!)
@[simp, grind .] lemma axiomCorfl [HasAxiomCorfl 𝓢] : 𝓢 ⊢ Axioms.Corefl φ ψ := ⟨axiomCorfl!⟩


class HasAxiomTra1 (𝓢 : S) where
  axiomTra1! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Tra1 φ ψ χ
export HasAxiomTra1 (axiomTra1!)
@[simp, grind .] lemma axiomTra1 [HasAxiomTra1 𝓢] : 𝓢 ⊢ Axioms.Tra1 φ ψ χ := ⟨axiomTra1!⟩


class HasAxiomTra2 (𝓢 : S) where
  axiomTra2! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Tra2 φ ψ χ
export HasAxiomTra2 (axiomTra2!)
@[simp, grind .] lemma axiomTra2 [HasAxiomTra2 𝓢] : 𝓢 ⊢ Axioms.Tra2 φ ψ χ := ⟨axiomTra2!⟩


class HasAxiomSer (𝓢 : S) where
  axiomSer! : 𝓢 ⊢! Axioms.Ser
export HasAxiomSer (axiomSer!)
@[simp, grind .] lemma axiomSer [HasAxiomSer 𝓢] : 𝓢 ⊢ Axioms.Ser := ⟨axiomSer!⟩


class HasAxiomSym (𝓢 : S) where
  axiomSym! {φ ψ : F} : 𝓢 ⊢! Axioms.Sym φ ψ
export HasAxiomSym (axiomSym!)
@[simp, grind .] lemma axiomSym [HasAxiomSym 𝓢] : 𝓢 ⊢ Axioms.Sym φ ψ := ⟨axiomSym!⟩


class HasAxiomPer (𝓢 : S) where
  axiomPer! {φ : F} : 𝓢 ⊢! Axioms.Per φ
export HasAxiomPer (axiomPer!)
@[simp, grind .] lemma axiomPer [HasAxiomPer 𝓢] : 𝓢 ⊢ Axioms.Per φ := ⟨axiomPer!⟩


end Entailment

end LO.Propositional
