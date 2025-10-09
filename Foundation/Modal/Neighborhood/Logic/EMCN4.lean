import Foundation.Modal.Neighborhood.Logic.EMCN
import Foundation.Modal.Neighborhood.Logic.ENT4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMCN4 (F : Frame) extends F.IsMonotonic, F.IsRegular, F.ContainsUnit, F.IsTransitive where
protected abbrev FrameClass.EMCN4 : FrameClass := { F | F.IsEMCN4 }

protected class Frame.IsFiniteEMCN4 (F : Frame) extends F.IsEMCN4, F.IsFinite where
protected abbrev FrameClass.finite_EMCN4 : FrameClass := { F | F.IsFiniteEMCN4 }

end Neighborhood

namespace EMCN4

instance Neighborhood.sound : Sound Modal.EMCN4 FrameClass.EMCN4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl | rfl) F hF <;>
  . replace hF := Set.mem_setOf_eq.mp hF;
    simp;

instance consistent : Entailment.Consistent Modal.EMCN4 := consistent_of_sound_frameclass FrameClass.EMCN4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance Neighborhood.complete : Complete Modal.EMCN4 FrameClass.EMCN4 := (supplementedMinimalCanonicity Modal.EMCN4).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.finite_complete : Complete Modal.EMCN4 FrameClass.finite_EMCN4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EMCN4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply quasiFilteringTransitiveFiltration M (Finset.toSet $ φ.subformulas ∪ (□⊤ : Formula ℕ).subformulas) (by simp) |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply quasiFilteringTransitiveFiltration.isTransitive.trans;
    mono := by apply quasiFilteringTransitiveFiltration.isMonotonic.mono;
    regular := by apply quasiFilteringTransitiveFiltration.isRegular.regular;
    contains_unit := by apply quasiFilteringTransitiveFiltration.containsUnit (by simp) |>.contains_unit;
  };
⟩

end EMCN4

end LO.Modal
