import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal

open Kripke
open Modal.Kripke


namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsKT4B := Frame.IsEquivalence
protected class Frame.IsFiniteKT4B (F : Frame) extends Frame.IsKT4B F, Frame.IsFinite F

abbrev FrameClass.KT4B : FrameClass := { F | F.IsKT4B }
abbrev FrameClass.finite_KT4B: FrameClass := { F | F.IsFiniteKT4B }

instance [F.IsKT4B] : F.IsS5 where
instance [F.IsS5] : F.IsKT4B where

end Kripke


instance : Sound Modal.KT4B FrameClass.KT4B := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomB_of_symmetric;

instance : Entailment.Consistent Modal.KT4B := consistent_of_sound_frameclass FrameClass.KT4B $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.KT4B FrameClass.KT4B := ⟨by constructor⟩

instance : Complete Modal.KT4B FrameClass.KT4B := inferInstance

open finestFiltrationTransitiveClosureModel in
instance : Complete Modal.KT4B FrameClass.finite_KT4B := ⟨by
  intro φ hp;
  apply Complete.complete (𝓜 := FrameClass.KT4B);
  intro F F_equiv V x;
  replace F_equiv := Set.mem_setOf_eq.mp F_equiv;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    symm := finestFiltrationTransitiveClosureModel.isSymmetric.symm
    refl := finestFiltrationTransitiveClosureModel.isReflexive.refl
  }
⟩

instance : Modal.S5 ≊ Modal.KT4B := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.S5) (FrameClass.KT4B);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.KT4B) (FrameClass.S5);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;

instance : Modal.S5 ≊ Modal.KT4B := inferInstance

end LO.Modal
