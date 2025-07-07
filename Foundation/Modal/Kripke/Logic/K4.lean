import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

abbrev Frame.IsK4 (F : Frame) := F.IsTransitive
class Frame.IsFiniteK4 (F : Frame) extends Frame.IsK4 F, Frame.IsFinite F

protected abbrev FrameClass.K4 : FrameClass := { F | F.IsK4 }
protected abbrev FrameClass.finite_K4 : FrameClass := { F | F.IsFiniteK4 }

end Kripke


namespace Logic.K4.Kripke

instance sound : Sound Logic.K4 FrameClass.K4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  apply validate_AxiomFour_of_transitive (trans := F_trans);

instance consistent : Entailment.Consistent Logic.K4 :=
  consistent_of_sound_frameclass FrameClass.K4 $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance canonical : Canonical Logic.K4 FrameClass.K4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Logic.K4 FrameClass.K4 := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finite_complete : Complete Logic.K4 FrameClass.finite_K4 := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Set.mem_setOf_eq.mpr;
  exact { world_finite := by apply FilterEqvQuotient.finite $ by simp }
⟩

lemma trans : Logic.K4 = FrameClass.K4.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K ⪱ Logic.K4 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K4 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.Kripke.all];
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≠ y⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor
      . trivial;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro x;
          match x with
          | 0 => tauto;
          | 1 => tauto;
        . exact ⟨1, by omega, 0, by omega, by trivial⟩;

end Logic.K4.Kripke

end LO.Modal
