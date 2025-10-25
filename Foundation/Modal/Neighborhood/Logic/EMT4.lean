import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.E4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

protected class Frame.IsEMT4 (F : Frame) extends F.IsMonotonic, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.EMT4 : FrameClass := { F | F.IsEMT4 }

protected class Frame.IsFiniteEMT4 (F : Frame) extends F.IsEMT4, F.IsFinite
protected abbrev FrameClass.finite_EMT4 : FrameClass := { F | F.IsFiniteEMT4 }

end Neighborhood


namespace EMT4

instance Neighborhood.sound : Sound Modal.EMT4 FrameClass.EMT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance consistent : Entailment.Consistent Modal.EMT4 := consistent_of_sound_frameclass FrameClass.EMT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.complete : Complete Modal.EMT4 FrameClass.EMT4 := (supplementedBasicCanonicity Modal.EMT4).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.finite_complete : Complete Modal.EMT4 FrameClass.finite_EMT4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EMT4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply supplementedTransitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply supplementedTransitiveFiltration.isTransitive.trans;
    mono := by apply supplementedTransitiveFiltration.isMonotonic.mono;
    refl := by apply supplementedTransitiveFiltration.isReflexive.refl;
  };
⟩

end EMT4

end LO.Modal
