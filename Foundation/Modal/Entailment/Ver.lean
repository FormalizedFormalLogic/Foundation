import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.Ver 𝓢]

def bot_of_dia : 𝓢 ⊢ ◇φ ➝ ⊥ := by
  have : 𝓢 ⊢ ∼◇φ ➝ (◇φ ➝ ⊥) := and₁' $ neg_equiv (𝓢 := 𝓢) (φ := ◇φ);
  exact this ⨀ (contra₀' (and₁' diaDuality) ⨀ by
    apply dni';
    apply axiomVer;
  );
lemma bot_of_dia! : 𝓢 ⊢! ◇φ ➝ ⊥ := ⟨bot_of_dia⟩

def bot_of_dia' (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ⊥ := bot_of_dia ⨀ h
lemma bot_of_dia'! (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! ⊥ := ⟨bot_of_dia' h.some⟩

namespace Ver

protected def axiomTc : 𝓢 ⊢ Axioms.Tc φ := imply₁' axiomVer
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ Ver.axiomTc⟩

protected def axiomL : 𝓢 ⊢ Axioms.L φ := imply₁' axiomVer
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ Ver.axiomL⟩

end Ver


end LO.Entailment
