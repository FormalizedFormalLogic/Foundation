module

public import Foundation.Modal.Kripke.Logic.Grz.Completeness
public import Foundation.Modal.Kripke.Logic.Triv
public import Foundation.Modal.Kripke.Logic.S5

@[expose] public section

namespace LO.Modal.Logic

open Entailment
open Formula
open Kripke
open Modal.Kripke

instance : Modal.S5 ⪱ Modal.S5Grz := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.universal);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { universal := by tauto }
      . simp [Semantics.Models, Satisfies];

instance : Modal.Grz ⪱ Modal.S5Grz := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Five (.atom 0)
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_Grz);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w _ => w = 0)⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by omega,
          trans := by omega;
          antisymm := by grind;
        };
      . simp [Satisfies];
        simp [M]
        grind;

instance : Modal.S4 ⪱ Modal.Triv := calc
  Modal.S4 ⪱ Modal.S5    := by infer_instance
  _        ⪱ Modal.S5Grz := by infer_instance
  _        ≊ Modal.Triv  := by infer_instance

instance : Sound Modal.S5Grz FrameClass.finite_Triv := by
  suffices Modal.S5Grz ≊ Modal.Triv by
    constructor;
    intro φ h;
    apply Sound.sound $ Entailment.Equiv.iff.mp this φ |>.mp h;
  infer_instance;

end LO.Modal.Logic
end
