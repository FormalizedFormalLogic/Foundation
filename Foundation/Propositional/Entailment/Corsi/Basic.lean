import Foundation.Propositional.Entailment.Minimal.Basic

namespace LO.Propositional

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ ξ : F}


namespace Axioms

variable (φ ψ χ ξ)

protected abbrev DistributeAndOr := (φ ⋏ (ψ ⋎ χ)) ➝ ((φ ⋏ ψ) ⋎ (φ ⋏ χ))

protected abbrev C := (φ ➝ ψ) ⋏ (φ ➝ χ) ➝ (φ ➝ (ψ ⋏ χ))

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

class AndIntroRule (𝓢 : S) where
  andIR! {φ ψ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! ψ → 𝓢 ⊢! φ ⋏ ψ

class DilemmaRule (𝓢 : S) where
  dilemma! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ χ → 𝓢 ⊢! ψ ➝ χ → 𝓢 ⊢! φ ⋎ ψ ➝ χ

class GreedyRule (𝓢 : S) where
  greedy! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ ➝ χ → 𝓢 ⊢! φ ➝ ψ ⋏ χ

class TransRule (𝓢 : S) where
  transRule! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! ψ ➝ χ → 𝓢 ⊢! φ ➝ χ

class HasDistributeAndOr (𝓢 : S) where
  distributeAndOr! {φ ψ χ : F} : 𝓢 ⊢! Axioms.DistributeAndOr φ ψ χ

class HasAxiomC (𝓢 : S) where
  axiomC! {φ ψ χ : F} : 𝓢 ⊢! Axioms.C φ ψ χ

class HasAxiomD (𝓢 : S) where
  axiomD! {φ ψ χ : F} : 𝓢 ⊢! Axioms.D φ ψ χ

class HasAxiomI (𝓢 : S) where
  axiomI! {φ ψ χ : F} : 𝓢 ⊢! Axioms.I φ ψ χ


class HasImpId (𝓢 : S) where
  impId! {φ : F} : 𝓢 ⊢! Axioms.ImpId φ


class HasAxiomRfl (𝓢 : S) where
  axiomRfl! {φ ψ : F} : 𝓢 ⊢! Axioms.Rfl φ ψ

class HasAxiomCorfl (𝓢 : S) where
  axiomCorfl! {φ ψ : F} : 𝓢 ⊢! Axioms.Corefl φ ψ

class HasAxiomTra1 (𝓢 : S) where
  axiomTra1! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Tra1 φ ψ χ

class HasAxiomTra2 (𝓢 : S) where
  axiomTra2! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Tra2 φ ψ χ

class HasAxiomSer (𝓢 : S) where
  axiomSer! : 𝓢 ⊢! Axioms.Ser

class HasAxiomSym (𝓢 : S) where
  axiomSym! {φ ψ : F} : 𝓢 ⊢! Axioms.Sym φ ψ

class HasAxiomPer (𝓢 : S) where
  axiomPer! {φ : F} : 𝓢 ⊢! Axioms.Per φ


namespace Corsi

alias orIntroL! := Entailment.or₁
alias orIntroR! := Entailment.or₂
alias andElimL! := Entailment.and₁
alias andElimR! := Entailment.and₂

alias orIntroL := Entailment.or₁!
alias orIntroR := Entailment.or₂!
alias andElimL := Entailment.and₁!
alias andElimR := Entailment.and₂!

attribute [simp, grind .]
  orIntroL orIntroR
  andElimL andElimR

alias A_intro_left := Entailment.A!_intro_left
alias A_intro_right := Entailment.A!_intro_right

export AFortiori (af!)
@[grind <=] lemma af [AFortiori 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ ➝ φ := λ ⟨h⟩ => ⟨af! h⟩

export AndIntroRule (andIR!)
@[grind <=] lemma andIR [AndIntroRule 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ → 𝓢 ⊢ φ ⋏ ψ := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨andIR! h₁ h₂⟩


export DilemmaRule (dilemma!)
@[grind <=] lemma dilemma [DilemmaRule 𝓢] : 𝓢 ⊢ φ ➝ χ → 𝓢 ⊢ ψ ➝ χ → 𝓢 ⊢ φ ⋎ ψ ➝ χ := λ ⟨a⟩ ⟨b⟩ => ⟨dilemma! a b⟩

alias CA!_of_C!_of_C! := dilemma!
alias CA_of_C_of_C := dilemma


export GreedyRule (greedy!)
@[grind <=] lemma greedy [GreedyRule 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ ➝ χ → 𝓢 ⊢ φ ➝ ψ ⋏ χ := λ ⟨a⟩ ⟨b⟩ => ⟨greedy! a b⟩

alias CK!_of_C!_of_C! := greedy!
alias CK_of_C_of_C := greedy


export TransRule (transRule!)
@[grind ⇐] lemma transRule [TransRule 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ ψ ➝ χ → 𝓢 ⊢ φ ➝ χ := λ ⟨a⟩ ⟨b⟩ => ⟨transRule! a b⟩

alias C_trans! := transRule!
alias C_trans := transRule


export HasDistributeAndOr (distributeAndOr!)
lemma distributeAndOr [HasDistributeAndOr 𝓢] : 𝓢 ⊢ Axioms.DistributeAndOr φ ψ χ := ⟨distributeAndOr!⟩

export HasAxiomC (axiomC!)
lemma axiomC [HasAxiomC 𝓢] : 𝓢 ⊢ Axioms.C φ ψ χ := ⟨axiomC!⟩

export HasAxiomD (axiomD!)
lemma axiomD [HasAxiomD 𝓢] : 𝓢 ⊢ Axioms.D φ ψ χ := ⟨axiomD!⟩

export HasAxiomI (axiomI!)
lemma axiomI [HasAxiomI 𝓢] : 𝓢 ⊢ Axioms.I φ ψ χ := ⟨axiomI!⟩

export HasImpId (impId!)
lemma impId [HasImpId 𝓢] : 𝓢 ⊢ Axioms.ImpId φ := ⟨impId!⟩


attribute [simp, grind .]
  distributeAndOr
  axiomC
  axiomD
  axiomI
  impId



export HasAxiomRfl (axiomRfl!)
lemma axiomRfl [HasAxiomRfl 𝓢] : 𝓢 ⊢ Axioms.Rfl φ ψ := ⟨axiomRfl!⟩


export HasAxiomCorfl (axiomCorfl!)
lemma axiomCorfl [HasAxiomCorfl 𝓢] : 𝓢 ⊢ Axioms.Corefl φ ψ := ⟨axiomCorfl!⟩


export HasAxiomTra1 (axiomTra1!)
lemma axiomTra1 [HasAxiomTra1 𝓢] : 𝓢 ⊢ Axioms.Tra1 φ ψ χ := ⟨axiomTra1!⟩

export HasAxiomTra2 (axiomTra2!)
lemma axiomTra2 [HasAxiomTra2 𝓢] : 𝓢 ⊢ Axioms.Tra2 φ ψ χ := ⟨axiomTra2!⟩


export HasAxiomSer (axiomSer!)
lemma axiomSer [HasAxiomSer 𝓢] : 𝓢 ⊢ Axioms.Ser := ⟨axiomSer!⟩


export HasAxiomSym (axiomSym!)
lemma axiomSym [HasAxiomSym 𝓢] : 𝓢 ⊢ Axioms.Sym φ ψ := ⟨axiomSym!⟩


export HasAxiomPer (axiomPer!)
lemma axiomPer [HasAxiomPer 𝓢] : 𝓢 ⊢ Axioms.Per φ := ⟨axiomPer!⟩

attribute [simp, grind .]
  axiomRfl
  axiomCorfl
  axiomTra1 axiomTra2
  axiomSer
  axiomSym
  axiomPer

end Corsi


end Entailment

end LO.Propositional
