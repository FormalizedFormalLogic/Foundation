import Foundation.IntProp.Hilbert2.WellKnown
import Foundation.IntProp.Kripke2.Hilbert.Soundness

namespace LO.IntProp

open Formula.Kripke

abbrev Kripke.ConnectedFrameClass : FrameClass := { F | Connected F }

instance : Kripke.ConnectedFrameClass.DefinedByFormula (Axioms.Dummett (.atom 0) (.atom 1)) := ⟨by
  rintro F;
  constructor;
  . rintro h φ ⟨_, rfl⟩;
    apply Formula.Kripke.ValidOnFrame.dum;
    exact h;
  . rintro h x y z ⟨Rxy, Ryz⟩;
    let V : Kripke.Valuation F := ⟨λ {v a} => match a with | 0 => y ≺ v | 1 => z ≺ v | _ => True, by
      intro w v Rwv a ha;
      split at ha;
      . exact F.rel_trans ha Rwv;
      . exact F.rel_trans ha Rwv;
      . tauto;
    ⟩;
    replace h : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) := by simpa using h;
    rcases Formula.Kripke.Satisfies.or_def.mp $ @h V x with (hi | hi);
    . right;
      simpa [Semantics.Realize, Satisfies, V] using hi Rxy;
    . left;
      simpa [Semantics.Realize, Satisfies, V] using hi Ryz;
⟩


instance : Kripke.ConnectedFrameClass.IsNonempty := ⟨by
  use ⟨Unit, λ _ _ => True, by simp [Reflexive], by simp [Transitive]⟩;
  simp [Connected];
⟩

open Kripke

namespace Hilbert.LC.Kripke

instance : ConnectedFrameClass.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.LC ConnectedFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.LC := Kripke.Hilbert.consistent_of_FrameClass ConnectedFrameClass

end Hilbert.LC.Kripke


end LO.IntProp
