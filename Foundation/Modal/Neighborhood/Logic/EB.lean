module

public import Foundation.Modal.Neighborhood.Logic.E

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood


@[reducible] protected alias Frame.IsEB := Frame.IsSymmetric
protected class Frame.IsFiniteEB (F : Frame) extends F.IsEB, F.IsFinite

protected abbrev FrameClass.EB : FrameClass := { F | F.IsEB }
protected abbrev FrameClass.finite_EB : FrameClass := { F | F.IsFiniteEB }


instance : Frame.simple_blackhole.IsSymmetric := by
  constructor;
  intro X x hx;
  simp_all [(show X ≠ ∅ by grind), Frame.box];

end Neighborhood

namespace EB

instance Neighborhood.sound : Sound Modal.EB FrameClass.EB := instSound_of_validates_axioms $ by
  simp only [Semantics.ModelsSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomB_of_isSymmetric;

instance consistent : Entailment.Consistent Modal.EB := consistent_of_sound_frameclass FrameClass.EB $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

end EB

end LO.Modal
end
