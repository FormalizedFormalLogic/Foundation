import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

namespace Kripke


section definability

open Formula.Kripke

variable {F : Kripke.Frame}

lemma weakConnected_of_validate_WeakDot2 (hCon : WeakConfluent F) : F ⊧ (Axioms.WeakDot2 (.atom 0) (.atom 1)) := by sorry

lemma validate_WeakDot2_of_weakConfluent : F ⊧ (Axioms.WeakDot2 (.atom 0) (.atom 1)) → WeakConfluent F := by sorry;

abbrev WeakConfluentFrameClass : FrameClass := { F | WeakConfluent F }

instance : WeakConfluentFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [WeakConfluent];

instance WeakConfluentFrameClass.DefinedByWeakDot2 : WeakConfluentFrameClass.DefinedBy {Axioms.WeakDot2 (.atom 0) (.atom 1)} := ⟨by
  intro F;
  constructor;
  . simpa using weakConnected_of_validate_WeakDot2;
  . simpa using validate_WeakDot2_of_weakConfluent;
⟩

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

lemma weakConfluent [Entailment.HasAxiomWeakDot2 𝓢] : WeakConfluent (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz, eyz⟩;
  by_contra hC;
  sorry;

end Canonical

end canonicality


end Kripke

end LO.Modal
