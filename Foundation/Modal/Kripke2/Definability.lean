import Foundation.Modal.Kripke2.Basic

namespace LO.Modal

namespace Kripke

variable {C : Kripke.FrameClass}

def FrameClass.definedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) := ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

def FrameClass.definedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := C.definedBy {φ}


-- lemma subst_instances (definedBy : C.definedBy Γ) (h : φ ∈ Γ) : ∀ s, F ⊧ φ  := by sorry;


def FiniteFrameClass.definedBy (C : Kripke.FiniteFrameClass) (Γ : Set (Formula ℕ)) := ∀ F, F ∈ C ↔ F.toFrame ⊧* Γ

def FiniteFrameClass.definedByFormula (C : Kripke.FiniteFrameClass) (φ : Formula ℕ) := C.definedBy {φ}

end Kripke

end LO.Modal
