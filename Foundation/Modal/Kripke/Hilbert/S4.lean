import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.preorder : FrameClass := { F | Reflexive F ∧ Transitive F }
abbrev Kripke.FiniteFrameClass.preorder : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel }

instance : Kripke.FrameClass.preorder.DefinedBy Hilbert.S4.axioms := by
  convert FrameClass.multiGeachean.definability' {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩};
  . unfold Kripke.FrameClass.preorder FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];
  . exact Hilbert.S4.eq_Geach;

namespace Hilbert.S4.Kripke

instance sound : Sound (Hilbert.S4) Kripke.FrameClass.preorder := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;
  . unfold Kripke.FrameClass.preorder FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];

instance consistent : Entailment.Consistent (Hilbert.S4) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance canonical : Canonical (Hilbert.S4) Kripke.FrameClass.preorder := ⟨⟨Canonical.reflexive, Canonical.transitive⟩⟩

instance complete : Complete (Hilbert.S4) Kripke.FrameClass.preorder := inferInstance

open finestFilterationTransitiveClosureModel in
instance finiteComplete : Complete (Hilbert.S4) Kripke.FiniteFrameClass.preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hp;
  . refine ⟨?_, ?_⟩;
    . exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
    . exact transitive;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.S4.Kripke

end LO.Modal
