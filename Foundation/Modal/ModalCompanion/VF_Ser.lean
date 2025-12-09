import Foundation.Modal.ModalCompanion.VF

namespace LO.Modal

open Entailment
open Propositional.Formula (gödelWeakTranslate)

section

namespace PLoN

protected class Frame.NP (F : Frame) where
  P_serial : ∀ x : F, ∃ y, x ≺[⊥] y

protected abbrev FrameClass.NP : PLoN.FrameClass := { F | Frame.NP F }

end PLoN

namespace NP.PLoN

axiom sound : Sound (Modal.NP) PLoN.FrameClass.NP
axiom complete : Complete (Modal.NP) PLoN.FrameClass.NP

end NP.PLoN

end

variable {φ : Propositional.Formula ℕ}

open provable_VF_of_provable_gödelWeakTranslated in
lemma provable_VF_Ser_of_provable_gödelWeakTranslated : Modal.NP ⊢ φᵍʷ → Propositional.VF_Ser ⊢ φ := by
  contrapose!;
  intro h;
  obtain ⟨M, x, _, H⟩ := Propositional.FMT.exists_model_world_of_not_validOnFrameClass $ Propositional.VF_Ser.FMT.complete.exists_countermodel_of_not_provable h;
  apply Modal.NP.PLoN.sound.not_provable_of_countermodel;
  apply Modal.PLoN.not_validOnFrameClass_of_exists_model_world;
  use lemma.translate M, x;
  constructor;
  . tauto;
  . apply lemma.not.mpr H;

end LO.Modal
