module

public import Foundation.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment
open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.Ver 𝓢]

def bot_of_dia : 𝓢 ⊢! ◇φ 🡒 ⊥ := by
  have : 𝓢 ⊢! ∼◇φ 🡒 (◇φ 🡒 ⊥) := K_left $ negEquiv (𝓢 := 𝓢) (φ := ◇φ);
  exact this ⨀ (contra (K_left diaDuality) ⨀ by
    apply dni';
    apply axiomVer;
  );
lemma bot_of_dia! : 𝓢 ⊢ ◇φ 🡒 ⊥ := ⟨bot_of_dia⟩

def bot_of_dia' (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! ⊥ := bot_of_dia ⨀ h
lemma bot_of_dia'! (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ⊥ := ⟨bot_of_dia' h.some⟩

namespace Ver

protected def axiomTc : 𝓢 ⊢! Axioms.Tc φ := C_of_conseq axiomVer
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ Ver.axiomTc⟩

protected def axiomL : 𝓢 ⊢! Axioms.L φ := C_of_conseq axiomVer
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ Ver.axiomL⟩

end Ver


end LO.Modal.Entailment
end
