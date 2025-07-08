import Foundation.Modal.Kripke.Logic.S4Point3McK
import Foundation.Modal.Kripke.Logic.S4Point4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point4McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesSobocinskiCondition, F.SatisfiesMcKinseyCondition where

instance [F.IsS4Point4McK] : F.IsS4Point3McK where

protected abbrev FrameClass.S4Point4McK : FrameClass := { F | F.IsS4Point4McK }


end Kripke


namespace Hilbert.S4Point4McK.Kripke

instance : Sound Hilbert.S4Point4McK FrameClass.S4Point4McK := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance : Entailment.Consistent Hilbert.S4Point4McK :=
  consistent_of_sound_frameclass FrameClass.S4Point4McK $ by
    use whitepoint;
    constructor;

instance : Canonical Hilbert.S4Point4McK FrameClass.S4Point4McK := ⟨by constructor⟩

instance : Complete Hilbert.S4Point4McK FrameClass.S4Point4McK := inferInstance


instance : Hilbert.S4Point3McK ⪱ Hilbert.S4Point4McK := by
  constructor;
  . apply Hilbert.Kripke.weakerThan_of_subset_frameClass FrameClass.S4Point3McK FrameClass.S4Point4McK;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Point4 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point3McK);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x ≤ y⟩, λ w a => w ≠ 1⟩;
      use M, 0;
      constructor
      . exact {
          refl := by omega,
          trans := by omega,
          mckinsey := by
            simp only [ne_eq, M];
            intro x;
            use 2;
            constructor <;> omega;
        }
      . suffices ∃ x, (0 : M) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M) ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 2;
        omega;

instance : Hilbert.S4Point4 ⪱ Hilbert.S4Point4McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.McK (.atom 0))
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point4);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . exact {
          refl := by tauto,
          trans := by tauto,
          sobocinski := by tauto
        }
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        trivial;

end Hilbert.S4Point4McK.Kripke

end LO.Modal
