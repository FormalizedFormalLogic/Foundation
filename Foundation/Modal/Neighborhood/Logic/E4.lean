import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Filtration

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsTransitive := by
  constructor;
  simp [Frame.box];

@[reducible] protected alias Frame.IsE4 := Frame.IsTransitive
protected class Frame.IsFiniteE4 (F : Frame) extends F.IsE4, F.IsFinite

protected abbrev FrameClass.E4 : FrameClass := { F | F.IsE4 }
protected abbrev FrameClass.finite_E4 : FrameClass := { F | F.IsFiniteE4 }


end Neighborhood

namespace E4

instance : Sound Modal.E4 FrameClass.E4 := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFour_of_isTransitive;

instance : Entailment.Consistent Modal.E4 := consistent_of_sound_frameclass FrameClass.E4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.E4 FrameClass.E4 := minimalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Complete Modal.E4 FrameClass.finite_E4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.E4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
  };
⟩

end E4

instance : Modal.E4 ⪱ Modal.ET4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E4);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => Set.univ⟩;
      constructor;
      . tauto;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

end LO.Modal
