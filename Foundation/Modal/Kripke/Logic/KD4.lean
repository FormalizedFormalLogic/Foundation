import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKD4 (F : Kripke.Frame) extends F.IsSerial, F.IsTransitive

protected abbrev FrameClass.KD4 : FrameClass := { F | F.IsKD4 }

end Kripke


namespace Hilbert.KD4.Kripke

instance : Sound Hilbert.KD4 FrameClass.KD4 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  rintro _ (rfl | rfl) F ⟨_, _⟩
  . exact validate_AxiomD_of_serial
  . exact validate_AxiomFour_of_transitive

instance : Entailment.Consistent Hilbert.KD4 := consistent_of_sound_frameclass
  FrameClass.KD4 $ by
    use whitepoint
    constructor

instance : Canonical Hilbert.KD4 FrameClass.KD4 := ⟨by
  apply Set.mem_setOf_eq.mpr
  constructor
⟩

instance : Complete Hilbert.KD4 FrameClass.KD4 := inferInstance


instance : Hilbert.KD ⪱ Hilbert.KD4 := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp
  . apply Entailment.not_weakerThan_iff.mpr
    use Axioms.Four (.atom 0)
    constructor
    . exact axiomFour!
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false
      constructor
      . exact { serial := by simp [Serial]; }
      . simp [Semantics.Realize, Satisfies]
        tauto

instance : Hilbert.K4 ⪱ Hilbert.KD4 := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.D (.atom 0))
    constructor
    . exact axiomD!
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0
      constructor
      . exact { trans := by simp; }
      . simp [Semantics.Realize, Satisfies]

end Hilbert.KD4.Kripke

instance : Modal.KD ⪱ Modal.KD4 := inferInstance

instance : Modal.K4 ⪱ Modal.KD4 := inferInstance

end LO.Modal
