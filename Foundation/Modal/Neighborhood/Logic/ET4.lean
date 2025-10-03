import Foundation.Modal.Neighborhood.Logic.E4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsReflexive := by
  constructor;
  intro X x;
  simp_all;

protected class Frame.IsET4 (F : Frame) extends F.IsReflexive, F.IsTransitive
protected class Frame.IsFiniteET4 (F : Frame) extends F.IsET4, F.IsFinite

protected abbrev FrameClass.ET4 : FrameClass := { F | F.IsET4 }
protected abbrev FrameClass.finite_ET4 : FrameClass := { F | F.IsFiniteET4 }

end Neighborhood



namespace ET4

instance : Sound Modal.ET4 FrameClass.ET4 := instSound_of_validates_axioms $ by
  constructor;
  rintro φ (rfl | rfl) F ⟨_, _⟩;
  . apply valid_axiomFour_of_isTransitive;
  . apply valid_axiomT_of_isReflexive;

instance : Entailment.Consistent Modal.ET4 := consistent_of_sound_frameclass FrameClass.ET4 $ by
  use Frame.simple_blackhole;
  constructor;

instance : Complete Modal.ET4 FrameClass.ET4 := (minimalCanonicity _).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Modal.ET4 FrameClass.finite_ET4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.ET4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
    refl := by apply transitiveFiltration.isReflexive.refl;
  };
⟩

end ET4

end LO.Modal
