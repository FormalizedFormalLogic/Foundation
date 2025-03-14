import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KB
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.refl_symm : FrameClass := { F | Reflexive F ∧ Symmetric F }

abbrev Kripke.FrameClass.finite_refl_symm: FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Symmetric F.Rel }

namespace Kripke.FrameClass.refl_symm

lemma isMultiGeachean : FrameClass.refl_symm = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.refl_symm.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKTB : Kripke.FrameClass.refl_symm.Validates Hilbert.KTB.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_refl, F_symm⟩ φ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive $ by assumption;
  . exact validate_AxiomB_of_symmetric $ by assumption;

end Kripke.FrameClass.refl_symm


namespace Hilbert.KTB.Kripke

instance sound : Sound (Hilbert.KTB) Kripke.FrameClass.refl_symm :=
  instSound_of_validates_axioms Kripke.FrameClass.refl_symm.validates_HilbertKTB

instance consistent : Entailment.Consistent (Hilbert.KTB) :=
  consistent_of_sound_frameclass Kripke.FrameClass.refl_symm (by simp)

instance canonical : Canonical (Hilbert.KTB) Kripke.FrameClass.refl_symm := ⟨⟨Canonical.reflexive, Canonical.symmetric⟩⟩

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
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . apply reflexive_filterOf_of_reflexive (finestFilterationModel.filterOf) F_refl;
  . exact finestFilterationModel.symmetric_of_symmetric F_symm;
⟩

end Hilbert.KTB.Kripke

end LO.Modal
