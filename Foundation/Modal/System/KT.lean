import Foundation.Modal.System.K

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.KT 𝓢]

def diaTc : 𝓢 ⊢ φ ➝ ◇φ := by
  apply impTrans'' ?_ (and₂' diaDuality);
  exact impTrans'' dni $ contra₀' axiomT;
@[simp] lemma diaTc! : 𝓢 ⊢! φ ➝ ◇φ := ⟨diaTc⟩

def diaTc' [HasDiaDuality 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ◇φ := diaTc ⨀ h
lemma diaTc'! [HasDiaDuality 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ◇φ := ⟨diaTc' h.some⟩

end LO.System
