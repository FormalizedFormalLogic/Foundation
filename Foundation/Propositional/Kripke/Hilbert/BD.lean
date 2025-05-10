import Foundation.Propositional.Hilbert.BD
import Foundation.Propositional.Kripke.AxiomBoundDepth
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev isDepthLt (n : ℕ+) : FrameClass := { F | F.IsDepthLt n }

end Kripke.FrameClass


namespace Hilbert.BD.Kripke

variable {n : ℕ+}

instance sound : Sound (Hilbert.BD n) (FrameClass.isDepthLt n) := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_BoundDepth_of_isDepthLt hF;

instance consistent : Entailment.Consistent (Hilbert.BD n) := consistent_of_sound_frameclass (FrameClass.isDepthLt n) $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  simp only [Frame.IsDepthLt, whitepoint, ne_eq, List.get_eq_getElem, and_true, and_imp];
  intro l hl₁ hl₂;
  apply List.nodup_iff_get_ne_get.not.mpr;
  push_neg;
  use ⟨0, by omega⟩, ⟨n, by omega⟩;
  simp only [ne_eq, Fin.mk.injEq, Fin.getElem_fin, and_true];
  apply PNat.ne_zero n |>.symm;

instance canonical : Canonical (Hilbert.BD n) (FrameClass.isDepthLt n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  sorry;
⟩

instance complete : Complete (Hilbert.BD n) (FrameClass.isDepthLt n) := inferInstance

end Hilbert.BD.Kripke

end LO.Propositional
