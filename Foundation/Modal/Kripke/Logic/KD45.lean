import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.KD4
import Foundation.Modal.Kripke.Logic.KD5
import Foundation.Modal.Kripke.Logic.K45

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKD45 (F : Kripke.Frame) extends F.IsSerial, F.IsTransitive, F.IsEuclidean

protected abbrev FrameClass.KD45 : FrameClass := { F | F.IsKD45 }

end Kripke



namespace Hilbert.KD45.Kripke

instance : Sound Hilbert.KD45 FrameClass.KD45 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance : Entailment.Consistent Hilbert.KD45 := consistent_of_sound_frameclass FrameClass.KD45 $ by
  use whitepoint;
  constructor;

instance : Canonical Hilbert.KD45 FrameClass.KD45 := ⟨by constructor⟩

instance : Complete Hilbert.KD45 FrameClass.KD45 := inferInstance


instance : Hilbert.KD4 ⪱ Hilbert.KD45 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => x = y ∨ x < y⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine { serial := by tauto, trans := by omega };
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> omega;

instance : Hilbert.KD5 ⪱ Hilbert.KD45 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD5)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . refine {
          serial := by
            intro x;
            match x with
            | 0 => use 1; tauto;
            | 1 => use 1; omega;
            | 2 => use 2; omega;
          reucl := by simp [RightEuclidean]; omega;
        };
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            constructor;
            . omega;
            . trivial;

instance : Hilbert.K45 ⪱ Hilbert.KD45 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K45)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => True⟩, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine { trans := by simp, reucl := by simp [RightEuclidean] }
      . simp [Semantics.Realize, Satisfies];

end Hilbert.KD45.Kripke

instance : Modal.KD4 ⪱ Modal.KD45 := inferInstance

instance : Modal.KD5 ⪱ Modal.KD45 := inferInstance

instance : Modal.K45 ⪱ Modal.KD45 := inferInstance

end LO.Modal
