import Foundation.Modal.LogicSymbol
import Foundation.Modal.Kripke.AxiomL

namespace LO.Modal

namespace Kripke

open Formula.Kripke

namespace Frame

/--
  In Boolos 1994, mentioned as _prewellordering_.
-/
class SatisfiesBoolosCondition (F : Frame) : Prop where
  boolos : ∀ x y : F, x ≺ y → ∀ z, x ≺ z ∨ z ≺ y

export SatisfiesBoolosCondition (boolos)

variable {F : Frame}

lemma valid_axiomI_of_transitive_satisfiesBoolosCondition [F.IsTransitive] [F.SatisfiesBoolosCondition] : F ⊧ (Axioms.I (.atom 0) (.atom 1)) := by
  intro V x;
  apply Satisfies.or_def.mpr;
  by_contra! hC;
  obtain ⟨⟨y, Rxy, hy₁, ⟨z, Ryz, hz⟩⟩, ⟨w, Rxw, hw₁, hw₂⟩⟩ := by simpa [Semantics.Models, Satisfies] using hC;
  clear hC;
  apply hz $ hw₁ z ?_;
  rcases F.boolos y z Ryz w with (Ryw | Rwz);
  . exfalso;
    obtain ⟨v, Rwv, hv⟩ := hw₂ $ hy₁ w Ryw;
    exact hv $ hy₁ _ $ F.trans Ryw Rwv;
  . assumption;

end Frame

end Kripke

end LO.Modal
