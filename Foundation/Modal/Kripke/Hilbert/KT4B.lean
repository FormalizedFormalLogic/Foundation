import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
abbrev Kripke.FrameClass.finite_symm_preorder: FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Transitive F.Rel ∧ Symmetric F.Rel }

namespace Kripke.FrameClass.symm_preorder

lemma isMultiGeachean : FrameClass.symm_preorder = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.symm_preorder.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKT4B : Kripke.FrameClass.symm_preorder.Validates Hilbert.KT4B.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive $ by assumption;
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . exact validate_AxiomB_of_symmetric $ by assumption;

end Kripke.FrameClass.symm_preorder


namespace Hilbert.KT4B.Kripke

instance sound : Sound (Hilbert.KT4B) Kripke.FrameClass.symm_preorder :=
  instSound_of_validates_axioms Kripke.FrameClass.symm_preorder.validates_HilbertKT4B

instance consistent : Entailment.Consistent (Hilbert.KT4B) :=
  consistent_of_sound_frameclass Kripke.FrameClass.symm_preorder (by simp)

instance canonical : Canonical (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.symmetric⟩⟩

instance complete : Complete (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := inferInstance

open finestFilterationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.KT4B) Kripke.FrameClass.finite_symm_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
  . exact finestFilterationTransitiveClosureModel.transitive;
  . exact symmetric_of_symmetric F_symm;
⟩

end Hilbert.KT4B.Kripke


end LO.Modal
