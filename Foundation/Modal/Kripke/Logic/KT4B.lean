import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsKT4B := Frame.IsEquivalence
protected class Frame.IsFiniteKT4B (F : Frame) extends Frame.IsKT4B F, Frame.IsFinite F

abbrev FrameClass.KT4B : FrameClass := { F | F.IsKT4B }
abbrev FrameClass.finite_KT4B: FrameClass := { F | F.IsFiniteKT4B }

end Kripke


namespace Logic.KT4B.Kripke

instance sound : Sound Logic.KT4B FrameClass.KT4B := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent Logic.KT4B := consistent_of_sound_frameclass FrameClass.KT4B $ by
  use whitepoint;
  constructor;

instance canonical : Canonical Logic.KT4B FrameClass.KT4B := ⟨by constructor⟩

instance complete : Complete Logic.KT4B FrameClass.KT4B := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finite_complete : Complete Logic.KT4B FrameClass.finite_KT4B := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
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

end Logic.KT4B.Kripke

lemma Logic.KT4B.Kripke.symm_preorder : Logic.KT4B = FrameClass.KT4B.logic := eq_hilbert_logic_frameClass_logic


end LO.Modal
