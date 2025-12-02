import Foundation.Propositional.Entailment.Minimal.Basic
import Foundation.Propositional.Entailment.Int.Basic

namespace LO.Propositional

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ ξ : F}


namespace Axioms

variable (φ ψ χ ξ)

protected abbrev DistributeAndOr := (φ ⋏ (ψ ⋎ χ)) ➝ ((φ ⋏ ψ) ⋎ (φ ⋏ χ))

protected abbrev CollectOrAnd := ((φ ⋎ ψ) ⋏ (φ ⋎ χ)) ➝ (φ ⋎ (ψ ⋏ χ))

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
protected abbrev Hrd := φ ➝ ⊤ ➝ φ

end Axioms


namespace Entailment


class AFortiori (𝓢 : S) where
  af! {φ ψ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! ψ ➝ φ

class AndIntroRule (𝓢 : S) where
  andIR! {φ ψ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! ψ → 𝓢 ⊢! φ ⋏ ψ

class HasDistributeAndOr (𝓢 : S) where
  distributeAndOr! {φ ψ χ : F} : 𝓢 ⊢! Axioms.DistributeAndOr φ ψ χ

class HasCollectOrAnd (𝓢 : S) where
  collectOrAnd! {φ ψ χ : F} : 𝓢 ⊢! Axioms.CollectOrAnd φ ψ χ

class HasAxiomC (𝓢 : S) where
  axiomC! {φ ψ χ : F} : 𝓢 ⊢! Axioms.C φ ψ χ

class RuleC (𝓢 : S) where
  ruleC! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! φ ➝ χ → 𝓢 ⊢! φ ➝ (ψ ⋏ χ)


class HasAxiomD (𝓢 : S) where
  axiomD! {φ ψ χ : F} : 𝓢 ⊢! Axioms.D φ ψ χ

class RuleD (𝓢 : S) where
  ruleD! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ χ → 𝓢 ⊢! ψ ➝ χ → 𝓢 ⊢! φ ⋎ ψ ➝ χ


class HasAxiomI (𝓢 : S) where
  axiomI! {φ ψ χ : F} : 𝓢 ⊢! Axioms.I φ ψ χ

class RuleI (𝓢 : S) where
  ruleI! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! ψ ➝ χ → 𝓢 ⊢! φ ➝ χ


class RuleE (𝓢 : S) where
  ruleE! {φ ψ χ ξ : F} : 𝓢 ⊢! φ ⭤ ψ → 𝓢 ⊢! χ ⭤ ξ → 𝓢 ⊢! (φ ➝ χ) ⭤ (ψ ➝ ξ)


class RuleRestall (𝓢 : S) where
  restall! {φ ψ χ ξ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! χ ➝ ξ → 𝓢 ⊢! (ψ ➝ χ) ➝ (φ ➝ ξ)


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

class HasAxiomHrd (𝓢 : S) where
  axiomHrd! {φ : F} : 𝓢 ⊢! Axioms.Hrd φ


namespace Corsi

alias orIntroL! := Entailment.or₁
alias orIntroR! := Entailment.or₂
alias andElimL! := Entailment.and₁
alias andElimR! := Entailment.and₂

alias orIntroL := Entailment.or₁!
alias orIntroR := Entailment.or₂!
alias andElimL := Entailment.and₁!
alias andElimR := Entailment.and₂!

alias efq! := Entailment.efq
alias efq := Entailment.efq!

attribute [simp, grind .]
  orIntroL orIntroR
  andElimL andElimR

alias A_intro_left := Entailment.A!_intro_left
alias A_intro_right := Entailment.A!_intro_right


alias K_Elim_left! := Entailment.K_left
alias K_Elim_right! := Entailment.K_right

alias K_Elim_left := Entailment.K!_left
alias K_Elim_right := Entailment.K!_right



alias of_O := Entailment.of_O!

export AFortiori (af!)
@[grind <=] lemma af [AFortiori 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ ➝ φ := λ ⟨h⟩ => ⟨af! h⟩

export AndIntroRule (andIR!)
@[grind <=] lemma andIR [AndIntroRule 𝓢] : 𝓢 ⊢ φ → 𝓢 ⊢ ψ → 𝓢 ⊢ φ ⋏ ψ := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨andIR! h₁ h₂⟩


export RuleC (ruleC!)
@[grind <=] lemma ruleC [RuleC 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ φ ➝ χ → 𝓢 ⊢ φ ➝ (ψ ⋏ χ) := λ ⟨a⟩ ⟨b⟩ => ⟨ruleC! a b⟩
alias CK!_of_C!_of_C! := ruleC!
alias CK_of_C_of_C := ruleC


export RuleD (ruleD!)
@[grind <=] lemma ruleD [RuleD 𝓢] : 𝓢 ⊢ φ ➝ χ → 𝓢 ⊢ ψ ➝ χ → 𝓢 ⊢ φ ⋎ ψ ➝ χ := λ ⟨a⟩ ⟨b⟩ => ⟨ruleD! a b⟩
alias CA!_of_C!_of_C! := ruleD!
alias CA_of_C_of_C := ruleD


export RuleI (ruleI!)
@[grind <=] lemma ruleI [RuleI 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ ψ ➝ χ → 𝓢 ⊢ φ ➝ χ := λ ⟨a⟩ ⟨b⟩ => ⟨ruleI! a b⟩
alias C_trans! := ruleI!
alias C_trans := ruleI


export RuleE (ruleE!)
@[grind <=] lemma ruleE [RuleE 𝓢] : 𝓢 ⊢ φ ⭤ ψ → 𝓢 ⊢ χ ⭤ ξ → 𝓢 ⊢ (φ ➝ χ) ⭤ (ψ ➝ ξ) := λ ⟨a⟩ ⟨b⟩ => ⟨ruleE! a b⟩


export RuleRestall (restall!)
@[grind <=] lemma restall [RuleRestall 𝓢] : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ χ ➝ ξ → 𝓢 ⊢ (ψ ➝ χ) ➝ (φ ➝ ξ) := λ ⟨a⟩ ⟨b⟩ => ⟨restall! a b⟩


export HasDistributeAndOr (distributeAndOr!)
lemma distributeAndOr [HasDistributeAndOr 𝓢] : 𝓢 ⊢ Axioms.DistributeAndOr φ ψ χ := ⟨distributeAndOr!⟩

export HasCollectOrAnd (collectOrAnd!)
lemma collectOrAnd [HasCollectOrAnd 𝓢] : 𝓢 ⊢ Axioms.CollectOrAnd φ ψ χ := ⟨collectOrAnd!⟩

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


export HasAxiomHrd (axiomHrd!)
lemma axiomHrd [HasAxiomHrd 𝓢] : 𝓢 ⊢ Axioms.Hrd φ := ⟨axiomHrd!⟩

attribute [simp, grind .]
  axiomRfl
  axiomCorfl
  axiomTra1 axiomTra2
  axiomSer
  axiomSym
  axiomHrd

section

def CK_right_cancel! [RuleI 𝓢] [RuleC 𝓢] [AFortiori 𝓢] [HasImpId 𝓢] (h₁ : 𝓢 ⊢! φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ➝ χ := by
  apply C_trans! ?_ h₁;
  apply CK!_of_C!_of_C!;
  . apply impId!;
  . apply af! h₂;
lemma CK_right_cancel [RuleI 𝓢] [RuleC 𝓢] [AFortiori 𝓢] [HasImpId 𝓢] (h₁ : 𝓢 ⊢ φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ➝ χ := ⟨CK_right_cancel! h₁.some h₂.some⟩

def CK_right_replace!  [RuleI 𝓢] [RuleC 𝓢] [Entailment.HasAxiomAndElim 𝓢] (h₁ : 𝓢 ⊢! φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢! ψ' ➝ ψ) : 𝓢 ⊢! φ ⋏ ψ' ➝ χ := by
  apply C_trans! ?_ h₁;
  apply CK!_of_C!_of_C!
  . apply andElimL!;
  . apply C_trans! ?_ h₂;
    apply andElimR!;
lemma CK_right_replace [RuleI 𝓢] [RuleC 𝓢] [Entailment.HasAxiomAndElim 𝓢] (h₁ : 𝓢 ⊢ φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢ ψ' ➝ ψ) : 𝓢 ⊢ φ ⋏ ψ' ➝ χ := ⟨CK_right_replace! h₁.some h₂.some⟩

def K_comm! [RuleC 𝓢] [Entailment.HasAxiomAndElim 𝓢] : 𝓢 ⊢! (φ ⋏ ψ) ➝ (ψ ⋏ φ) := CK!_of_C!_of_C! andElimR! andElimL!
@[simp, grind .] lemma K_comm [RuleC 𝓢] [Entailment.HasAxiomAndElim 𝓢] : 𝓢 ⊢ (φ ⋏ ψ) ➝ (ψ ⋏ φ) := ⟨K_comm!⟩

def A_comm! [RuleD 𝓢] [Entailment.HasAxiomOrInst 𝓢] : 𝓢 ⊢! (φ ⋎ ψ) ➝ (ψ ⋎ φ) := CA!_of_C!_of_C! orIntroR! orIntroL!
@[simp, grind .] lemma A_comm [RuleD 𝓢] [Entailment.HasAxiomOrInst 𝓢] : 𝓢 ⊢ (φ ⋎ ψ) ➝ (ψ ⋎ φ) := ⟨A_comm!⟩

def equivId! [HasImpId 𝓢] [AndIntroRule 𝓢] : 𝓢 ⊢! φ ⭤ φ := andIR! impId! impId!
@[simp, grind .] lemma equivId [HasImpId 𝓢] [AndIntroRule 𝓢] : 𝓢 ⊢ φ ⭤ φ := ⟨equivId!⟩

end

end Corsi


end Entailment

end LO.Propositional
