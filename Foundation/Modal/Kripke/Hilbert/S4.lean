import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.preorder : FrameClass := { F | Reflexive F ∧ Transitive F }
abbrev Kripke.FrameClass.finite_preorder: FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Transitive F.Rel }

namespace Kripke.FrameClass.preorder

lemma isMultiGeachean : FrameClass.preorder = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.transitive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.preorder.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertS4 : Kripke.FrameClass.preorder.Validates Hilbert.S4.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_refl, F_trans⟩ φ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive F_refl;
  . exact validate_AxiomFour_of_transitive F_trans;

end Kripke.FrameClass.preorder


namespace Hilbert.S4.Kripke

instance sound : Sound (Hilbert.S4) Kripke.FrameClass.preorder :=
  instSound_of_validates_axioms Kripke.FrameClass.preorder.validates_HilbertS4

instance consistent : Entailment.Consistent (Hilbert.S4) :=
  consistent_of_sound_frameclass Kripke.FrameClass.preorder (by simp)

instance canonical : Canonical (Hilbert.S4) Kripke.FrameClass.preorder := ⟨⟨Canonical.reflexive, Canonical.transitive⟩⟩

instance complete : Complete (Hilbert.S4) Kripke.FrameClass.preorder := inferInstance

open finestFilterationTransitiveClosureModel in
instance finiteComplete : Complete (Hilbert.S4) Kripke.FrameClass.finite_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, ?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . exact reflexive_of_transitive_reflexive F_trans F_refl;
  . exact finestFilterationTransitiveClosureModel.transitive;
⟩

end Hilbert.S4.Kripke

end LO.Modal
