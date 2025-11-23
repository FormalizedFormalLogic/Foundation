import Foundation.Propositional.Entailment.Corsi.Basic

namespace LO.Propositional

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

protected class VF (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasDistributeAndOr 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomC 𝓢,
  Entailment.HasAxiomVerum 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢,
  Entailment.DilemmaRule 𝓢,
  Entailment.GreedyRule 𝓢,
  Entailment.TransRule 𝓢

-- TODO: unify old
namespace Corsi

variable [Entailment.VF 𝓢]

/-
def C_trans! (h₁ : 𝓢 ⊢! φ ➝ ψ) (h₂ : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ➝ χ := by
  refine (axiomI! (ψ := ψ)) ⨀ ?_;
  apply andIR! <;> assumption;
@[grind ⇐] lemma C_trans (h₁ : 𝓢 ⊢ φ ➝ ψ) (h₂ : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ➝ χ := ⟨C_trans! h₁.some h₂.some⟩

def CK_right_cancel! (h₁ : 𝓢 ⊢! φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ➝ χ := by
  apply C_trans! ?_ h₁;
  apply CK!_of_C!_of_C!;
  . apply impId!;
  . apply af! h₂;
lemma CK_right_cancel (h₁ : 𝓢 ⊢ φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ➝ χ := ⟨CK_right_cancel! h₁.some h₂.some⟩

def CK_right_replace! (h₁ : 𝓢 ⊢! φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢! ψ' ➝ ψ) : 𝓢 ⊢! φ ⋏ ψ' ➝ χ := by
  apply C_trans! ?_ h₁;
  apply CK!_of_C!_of_C!
  . apply andElimL!;
  . apply C_trans! ?_ h₂;
    apply andElimR!;
lemma CK_right_replace (h₁ : 𝓢 ⊢ φ ⋏ ψ ➝ χ) (h₂ : 𝓢 ⊢ ψ' ➝ ψ) : 𝓢 ⊢ φ ⋏ ψ' ➝ χ := ⟨CK_right_replace! h₁.some h₂.some⟩
-/

end Corsi



end Entailment


end LO.Propositional
