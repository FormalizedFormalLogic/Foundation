import Foundation.Modal.System.K

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.KTc 𝓢]

def diaT : 𝓢 ⊢ ◇φ ➝ φ := by
  apply impTrans'' (and₁' diaDuality) ?_;
  apply contra₂';
  exact axiomTc;
@[simp] lemma diaT! : 𝓢 ⊢! ◇φ ➝ φ := ⟨diaT⟩

def diaT' (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ φ := diaT ⨀ h
lemma diaT'! (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! φ := ⟨diaT' h.some⟩


namespace KTc

variable [System.KTc 𝓢]

protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := axiomTc
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ KTc.axiomFour⟩

protected def axiomFive : 𝓢 ⊢ ◇φ ➝ □◇φ := axiomTc
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ KTc.axiomFive⟩

end KTc


end LO.System
