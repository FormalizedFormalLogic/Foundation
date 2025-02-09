import Foundation.IntProp.Hilbert2.WellKnown
import Foundation.IntProp.Kripke2.Hilbert.Soundness

namespace LO.IntProp

open Kripke
open Formula.Kripke


abbrev Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }

instance : Kripke.EuclideanFrameClass.DefinedByFormula (Axioms.LEM (.atom 0)) := ⟨by
  rintro F;
  constructor;
  . rintro hEucl _ ⟨_, rfl⟩;
    apply ValidOnFrame.lem;
    apply symm_of_refl_eucl;
    . exact F.rel_refl;
    . assumption;
  . rintro h x y z Rxy Rxz;
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
⟩

instance : Kripke.EuclideanFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Euclidean];
⟩


open Kripke

namespace Hilbert.Cl.Kripke

instance : EuclideanFrameClass.DefinedBy (Hilbert.Cl.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.Cl EuclideanFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.Cl := Kripke.Hilbert.consistent_of_FrameClass EuclideanFrameClass

end Hilbert.Cl.Kripke


end LO.IntProp
