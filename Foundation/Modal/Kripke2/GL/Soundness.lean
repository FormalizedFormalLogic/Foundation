import Foundation.Modal.Kripke2.AxiomL
import Foundation.Modal.Kripke2.Soundness
import Foundation.Modal.Hilbert2.WellKnown

namespace LO.Modal.Hilbert.GL.Kripke

open Kripke
open System

instance finiteSound : Sound Hilbert.GL Kripke.TransitiveIrreflexiveFiniteFrameClass := by
  -- haveI := FrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL
  sorry;

instance consistent : System.Consistent Hilbert.GL := by
  -- haveI := FrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL
  sorry;

end LO.Modal.Hilbert.GL.Kripke

#min_imports
