import Foundation.Modal.Hilbert2.K
import Foundation.Modal.Kripke2.Hilbert.Soundness
import Foundation.Modal.Kripke2.Completeness

namespace LO.Modal

instance : Kripke.AllFrameClass.DefinedBy (Hilbert.K.axioms) := ⟨by
  suffices ∀ F, ∀ φ ∈ Hilbert.K.axioms, Formula.Kripke.ValidOnFrame F φ by simpa;
  rintro F _ ⟨ψ, ⟨_, rfl⟩, ⟨s, rfl⟩⟩;
  apply Formula.Kripke.ValidOnFrame.axiomK;
⟩

namespace Hilbert.K

instance : System.Consistent (Hilbert.K) := Kripke.Hilbert.instConsistent (C := Kripke.AllFrameClass) ⟨⟨Fin 1, λ _ _ => True⟩, by trivial⟩

instance : Complete (Hilbert.K) (Kripke.AllFrameClass) := Kripke.instCompleteOfCanonical trivial

end Hilbert.K

end LO.Modal
