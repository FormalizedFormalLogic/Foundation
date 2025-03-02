import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Completeness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_LEM_of_euclidean (hEuc : Euclidean F) : F ⊧ (Axioms.LEM (.atom 0)) := by
  apply ValidOnFrame.lem;
  apply symm_of_refl_eucl;
  . exact F.rel_refl;
  . assumption;

lemma euclidean_of_validate_LEM : F ⊧ (Axioms.LEM (.atom 0)) → Euclidean F := by
  rintro h x y z Rxy Rxz;
  let V : Kripke.Valuation F := ⟨λ {v a} => z ≺ v, by
    intro w v Rwv a Rzw;
    exact F.rel_trans' Rzw Rwv;
  ⟩;
  suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
  apply V.hereditary Rxy;
  simp at h;
  have := @h V x;
  simp [Semantics.Realize, Satisfies, V, or_iff_not_imp_right] at this;
  apply this z;
  . exact Rxz;
  . apply F.rel_refl;

abbrev EuclideanFrameClass : FrameClass := { F | Euclidean F }

instance EuclideanFrameClass.DefinedByAxiomLEM : EuclideanFrameClass.DefinedBy {Axioms.LEM (.atom 0)} := ⟨by
  intro F;
  constructor;
  . simpa using validate_LEM_of_euclidean;
  . simpa using euclidean_of_validate_LEM;
⟩

instance : EuclideanFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Euclidean];
⟩

end definability

end Kripke

end LO.Propositional
