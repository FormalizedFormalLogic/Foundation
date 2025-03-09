import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.refl_symm : FrameClass := { F | Reflexive F ∧ Symmetric F }
abbrev Kripke.FiniteFrameClass.refl_symm : FiniteFrameClass := { F | Reflexive F.Rel ∧ Symmetric F.Rel }

namespace Hilbert.KTB.Kripke

instance sound : Sound (Hilbert.KTB) Kripke.FrameClass.refl_symm := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.refl_symm FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def];

instance consistent : Entailment.Consistent (Hilbert.KTB) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance canonical : Canonical (Hilbert.KTB) Kripke.FrameClass.refl_symm := ⟨⟨Canonical.reflexive, Canonical.symmetric⟩⟩

instance complete : Complete (Hilbert.KTB) Kripke.FrameClass.refl_symm := inferInstance

instance finite_complete : Complete (Hilbert.KTB) Kripke.FiniteFrameClass.refl_symm := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationModel M φ.subformulas;
  apply filteration FM (finestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hp;
  . refine ⟨?_, ?_⟩;
    . apply reflexive_filterOf_of_reflexive (finestFilterationModel.filterOf);
      exact F_refl;
    . exact finestFilterationModel.symmetric_of_symmetric F_symm;;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.KTB.Kripke

end LO.Modal
