import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.Logic.Triv
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal.Logic

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

instance : Hilbert.S5 ⪱ Hilbert.S5Grz := by
  constructor;
  . exact Hilbert.Normal.weakerThan_of_subset_axioms (by simp)
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.universal);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { universal := by tauto }
      . simp [Semantics.Realize, Satisfies];
        tauto;

instance : Hilbert.Grz ⪱ Hilbert.S5Grz := by
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
          antisymm := by simp [M]; omega;
        };
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

instance : Hilbert.S4 ⪱ Hilbert.Triv := calc
  Hilbert.S4 ⪱ Hilbert.S5    := by infer_instance
  _          ⪱ Hilbert.S5Grz := by infer_instance
  _          ≊ Hilbert.Triv  := by infer_instance

instance : Sound Hilbert.S5Grz FrameClass.finite_Triv := by
  suffices Hilbert.S5Grz ≊ Hilbert.Triv by
    constructor;
    intro φ h;
    apply Sound.sound $ Entailment.Equiv.iff.mp this φ |>.mp h;
  infer_instance;

end LO.Modal.Logic
