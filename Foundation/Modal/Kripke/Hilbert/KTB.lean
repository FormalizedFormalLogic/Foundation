import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KB
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.refl_symm : FrameClass := { F | IsRefl _ F ∧ IsSymm _ F }

abbrev Kripke.FrameClass.finite_refl_symm: FrameClass := { F | Finite F.World ∧ IsRefl _ F ∧ IsSymm _ F }

namespace Hilbert.KTB.Kripke

instance sound : Sound (Hilbert.KTB) Kripke.FrameClass.refl_symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KTB) := consistent_of_sound_frameclass
  Kripke.FrameClass.refl_symm $ by
    use whitepoint;
    constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KTB) Kripke.FrameClass.refl_symm :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KTB) Kripke.FrameClass.refl_symm := inferInstance

instance finite_complete : Complete (Hilbert.KTB) Kripke.FrameClass.finite_refl_symm := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationModel M φ.subformulas;
  apply filteration FM (finestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, ?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . apply Kripke.finestFilterationModel.isRefl;
  . apply Kripke.finestFilterationModel.isSymm;
⟩

end Hilbert.KTB.Kripke

end LO.Modal
