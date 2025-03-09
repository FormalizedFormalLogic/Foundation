import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.symm_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
abbrev Kripke.FiniteFrameClass.symm_preorder : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ Symmetric F.Rel }

namespace Hilbert.KT4B.Kripke

instance consistent : Entailment.Consistent (Hilbert.KT4B) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance canonical : Canonical (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.symmetric⟩⟩

instance complete : Complete (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := inferInstance

open finestFilterationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.KT4B) Kripke.FiniteFrameClass.symm_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hp;
  . refine ⟨?_, ?_, ?_⟩;
    . exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
    . exact transitive;
    . exact symmetric_of_symmetric F_symm;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.KT4B.Kripke


end LO.Modal
