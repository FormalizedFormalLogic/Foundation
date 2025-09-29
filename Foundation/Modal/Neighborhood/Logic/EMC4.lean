import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EMC

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC4 (F : Frame) extends F.IsMonotonic, F.IsRegular, F.IsTransitive where
protected abbrev FrameClass.EMC4 : FrameClass := { F | F.IsEMC4 }

protected class Frame.IsFiniteEMC4 (F : Frame) extends F.IsEMC4, F.IsFinite where
protected abbrev FrameClass.finite_EMC4 : FrameClass := { F | F.IsFiniteEMC4 }

end Neighborhood

namespace EMC4

instance : Sound Modal.EMC4 FrameClass.EMC4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMC4 := consistent_of_sound_frameclass FrameClass.EMC4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Modal.EMC4 FrameClass.EMC4 := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Modal.EMC4 FrameClass.finite_EMC4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EMC4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply quasiFilteringTransitiveFiltration M φ.subformulas (by simp) |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply quasiFilteringTransitiveFiltration.isTransitive.trans;
    mono := by apply quasiFilteringTransitiveFiltration.isMonotonic.mono;
    regular := by apply quasiFilteringTransitiveFiltration.isRegular.regular;
  };
⟩

end EMC4

instance : Modal.EMC ⪱ Modal.EMC4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.trivial_nontransitive;
      constructor;
      . constructor;
      . simp;

instance : Modal.EMC4 ⪱ Modal.EMCT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.T (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC4);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => Set.univ⟩;
      constructor;
      . exact {
          mono := by simp,
          regular := by simp [Frame.box],
          trans := by simp [Frame.box]
        }
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

end LO.Modal
