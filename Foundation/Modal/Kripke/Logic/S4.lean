import Foundation.Modal.Entailment.KT
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.KD4
import Foundation.Modal.Kripke.Logic.KT

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

protected abbrev Frame.IsS4 := Frame.IsPreorder
protected class Frame.IsFiniteS4 (F : Frame) extends F.IsFinite, F.IsS4

protected abbrev FrameClass.S4 : FrameClass := { F | F.IsS4 }
protected abbrev FrameClass.finite_S4 : FrameClass := { F | F.IsFiniteS4 }

end Kripke


namespace Logic.S4.Kripke

instance sound : Sound Logic.S4 FrameClass.S4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent Logic.S4 := consistent_of_sound_frameclass FrameClass.S4 $ by
  use whitepoint;
  constructor;

instance canonical : Canonical Logic.S4 FrameClass.S4 := ⟨by constructor⟩

instance complete : Complete Logic.S4 FrameClass.S4 := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finiteComplete : Complete Logic.S4 FrameClass.finite_S4 := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  rintro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM filterOf (by simp) |>.mpr;
  apply hp;
  refine {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    refl := finestFiltrationTransitiveClosureModel.isReflexive.refl
  }
⟩

end Logic.S4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4.Kripke.preorder : Logic.S4 = FrameClass.S4.logic := eq_hilbert_logic_frameClass_logic

@[simp]
instance : Logic.KT ⪱ Logic.S4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomT!]) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬FrameClass.KT ⊧ φ by
      rw [KT.Kripke.refl];
      tauto;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => (x = 0 ∧ y ≠ 2) ∨ (x = 1 ∧ y ≠ 0) ∨ (x = 2 ∧ y = 2)⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . exact { refl := by omega };
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y hy;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => omega;
        . use 1;
          constructor;
          . omega;
          . use 2;
            refine ⟨by omega;, by trivial, by trivial⟩;

@[simp]
instance : Logic.KD4 ⪱ Logic.S4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬FrameClass.KD4 ⊧ φ by
      rw [KD4.Kripke.serial_trans];
      tauto;
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . refine {
          serial := by simp [Serial],
          trans := by simp
        };
      . simp [Semantics.Realize, Satisfies];

@[simp]
lemma S4.proper_extension_of_KD : Logic.KD ⪱ Logic.S4 := by trans Logic.KT <;> simp;

end Logic

end LO.Modal
