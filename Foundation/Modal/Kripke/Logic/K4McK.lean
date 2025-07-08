import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomMcK

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

class Frame.IsK4McK (F : Kripke.Frame) extends F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.K4McK : FrameClass := { F | F.IsK4McK }

end Kripke


namespace Hilbert.K4McK.Kripke

instance : Sound Hilbert.K4McK FrameClass.K4McK := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;

instance : Entailment.Consistent Hilbert.K4McK := consistent_of_sound_frameclass FrameClass.K4McK $ by
  use whitepoint;
  constructor;

instance : Canonical Hilbert.K4McK FrameClass.K4McK := ⟨by constructor⟩

instance : Complete Hilbert.K4McK FrameClass.K4McK := inferInstance

lemma trans_mckinsey : Modal.K4McK = FrameClass.K4McK.logic := eq_hilbert_logic_frameClass_logic

instance : Hilbert.K4 ⪱ Hilbert.K4McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.McK (.atom 0));
    constructor;
    . exact axiomMcK!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . simp only [Set.mem_setOf_eq]; refine { trans := by simp; }
      . simp [Semantics.Realize, Satisfies];

end Hilbert.K4McK.Kripke

instance : Modal.K4 ⪱ Modal.K4McK := inferInstance

end LO.Modal
