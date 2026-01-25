module

public import Foundation.Modal.Entailment.KT
public import Foundation.Modal.Kripke.Filtration
public import Foundation.Modal.Kripke.Logic.KD4
public import Foundation.Modal.Kripke.Logic.KT

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected abbrev Frame.IsS4 := Frame.IsPreorder
protected class Frame.IsFiniteS4 (F : Frame) extends F.IsFinite, F.IsS4

protected abbrev FrameClass.S4 : FrameClass := { F | F.IsS4 }
protected abbrev FrameClass.finite_S4 : FrameClass := { F | F.IsFiniteS4 }

end Kripke


namespace S4

instance : Sound Modal.S4 FrameClass.S4 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;

instance : Entailment.Consistent Modal.S4 := consistent_of_sound_frameclass FrameClass.S4 $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.S4 FrameClass.S4 := ⟨by constructor⟩

instance : Complete Modal.S4 FrameClass.S4 := inferInstance

open finestFiltrationTransitiveClosureModel in
instance : Complete Modal.S4 FrameClass.finite_S4 := ⟨by
  intro φ hp;
  apply Complete.complete (𝓜 := FrameClass.S4);
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


instance : Modal.KT ⪱ Modal.S4 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KT)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => (x = 0 ∧ y ≠ 2) ∨ (x = 1 ∧ y ≠ 0) ∨ (x = 2 ∧ y = 2)⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . exact { refl := by omega };
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [M, Semantics.Models, Satisfies];
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

instance : Modal.KD4 ⪱ Modal.S4 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . refine {
          serial := by simp [Serial],
          trans := by simp
        };
      . simp [Semantics.Models, Satisfies];
        grind;

instance : Modal.KD ⪱ Modal.S4 := calc
  Modal.KD ⪱ Modal.KD4 := by infer_instance
  _          ⪱ Modal.S4  := by infer_instance

end S4



instance : Sound Modal.S4 FrameClass.S4 := inferInstance
instance : Complete Modal.S4 FrameClass.S4 := inferInstance

end LO.Modal
end
