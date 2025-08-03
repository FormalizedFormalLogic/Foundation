import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K45
import Foundation.Modal.Kripke.Logic.KB

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsKB4 (F : Kripke.Frame) extends F.IsSymmetric, F.IsTransitive

protected abbrev FrameClass.KB4 : FrameClass := { F | F.IsKB4 }

instance [F.IsKB4] : F.IsK45 where

end Kripke


namespace Logic.KB4.Kripke

instance : Sound Hilbert.KB4 FrameClass.KB4 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFour_of_transitive;

instance : Entailment.Consistent Hilbert.KB4 := consistent_of_sound_frameclass FrameClass.KB4 $ by
  use whitepoint;
  constructor;

instance : Canonical Hilbert.KB4 FrameClass.KB4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor
⟩

instance : Complete Hilbert.KB4 FrameClass.KB4 := inferInstance

end Logic.KB4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke


instance : Hilbert.K45 ⪱ Hilbert.KB4 := by
  constructor;
  . apply Hilbert.Kripke.weakerThan_of_subset_frameClass FrameClass.K45 FrameClass.KB4;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K45);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . simp only [Fin.isValue, Set.mem_setOf_eq];
        refine { trans := by omega, reucl := by tauto };
      . simp [Semantics.Realize, Satisfies];

instance : Hilbert.KB ⪱ Hilbert.KB4 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KB);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . simp only [bne_iff_ne, ne_eq, Set.mem_setOf_eq];
        refine { symm := by tauto };
      . simp [Semantics.Realize, Satisfies];
        tauto;

end Logic

instance : Modal.K45 ⪱ Modal.KB4 := inferInstance

instance : Modal.KB ⪱ Modal.KB4 := inferInstance

end LO.Modal
