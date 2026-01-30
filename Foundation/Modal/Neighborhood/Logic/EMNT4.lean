module

public import Foundation.Modal.Neighborhood.Logic.EMT
public import Foundation.Modal.Neighborhood.Logic.EMN
public import Foundation.Modal.Neighborhood.Logic.ENT4

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

protected class Frame.IsEMNT4 (F : Frame) extends F.IsMonotonic, F.ContainsUnit, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.EMNT4 : FrameClass := { F | F.IsEMNT4 }

protected class Frame.IsFiniteEMNT4 (F : Frame) extends F.IsEMNT4, F.IsFinite
protected abbrev FrameClass.finite_EMNT4 : FrameClass := { F | F.IsFiniteEMNT4 }

end Neighborhood


namespace EMNT4

instance Neighborhood.sound : Sound Modal.EMNT4 FrameClass.EMNT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl | rfl) F hF <;>
  . replace hF := Set.mem_setOf_eq.mp hF;
    simp;

instance consistent : Entailment.Consistent Modal.EMNT4 := consistent_of_sound_frameclass FrameClass.EMNT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.complete : Complete Modal.EMNT4 FrameClass.EMNT4 := (supplementedBasicCanonicity Modal.EMNT4).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

/-- FFP of `Modal.EMNT4` -/
instance Neighborhood.finite_complete : Complete Modal.EMNT4 FrameClass.finite_EMNT4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EMNT4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply supplementedTransitiveFiltration M (Finset.toSet $ φ.subformulas ∪ (□⊤ : Formula ℕ).subformulas) |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply supplementedTransitiveFiltration.isTransitive.trans;
    mono := by apply supplementedTransitiveFiltration.isMonotonic.mono;
    refl := by apply supplementedTransitiveFiltration.isReflexive.refl;
    contains_unit := by apply supplementedTransitiveFiltration.containsUnit (by simp) |>.contains_unit;
  };
⟩

end EMNT4

end LO.Modal
end
