import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.E4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMT4 (F : Frame) extends F.IsMonotonic, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.EMT4 : FrameClass := { F | F.IsEMT4 }

protected class Frame.IsFiniteEMT4 (F : Frame) extends F.IsEMT4, F.IsFinite
protected abbrev FrameClass.finite_EMT4 : FrameClass := { F | F.IsFiniteEMT4 }

end Neighborhood


namespace EMT4

instance : Sound Modal.EMT4 FrameClass.EMT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMT4 := consistent_of_sound_frameclass FrameClass.EMT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Modal.EMT4 FrameClass.EMT4 := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Modal.EMT4 FrameClass.finite_EMT4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EMT4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply supplementedTransitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply supplementedTransitiveFiltration.isTransitive.trans;
    mono := by apply supplementedTransitiveFiltration.isMonotonic.mono;
    refl := by apply supplementedTransitiveFiltration.isReflexive.refl;
  };
⟩

end EMT4

instance : Modal.EMT ⪱ Modal.EMT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMT);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.trivial_nontransitive;
      constructor;
      . constructor;
      . simp;

instance : Modal.EMT4 ⪱ Modal.EMCT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.C (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMT4);
      apply not_validOnFrameClass_of_exists_model_world;
      use {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {1}, {0, 1}}
          | 1 => {{1}, {0, 1}},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      }, 0;
      constructor;
      . exact {
          mono := by sorry;
          refl := by
            simp [Frame.box];
            rintro X w;
            match w with
            | 0 => simp; sorry;
            | 1 => simp; sorry;
          trans := by

            sorry;
        }
      . simp! [Semantics.Realize, Satisfies];
        tauto_set;

end LO.Modal
