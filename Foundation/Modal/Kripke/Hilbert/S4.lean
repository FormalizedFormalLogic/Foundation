import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean


namespace Kripke

protected abbrev FrameClass.preorder : FrameClass := { F | IsPreorder _ F }

protected abbrev FrameClass.finite_preorder: FrameClass := { F | Finite F.World ∧ IsPreorder _ F.Rel }

end Kripke


namespace Hilbert.S4.Kripke

instance sound : Sound (Hilbert.S4) Kripke.FrameClass.preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.S4) := consistent_of_sound_frameclass Kripke.FrameClass.preorder $ by
  use whitepoint;
  constructor;

instance canonical : Canonical (Hilbert.S4) Kripke.FrameClass.preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
⟩

instance complete : Complete (Hilbert.S4) Kripke.FrameClass.preorder := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finiteComplete : Complete (Hilbert.S4) Kripke.FrameClass.finite_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  rintro F F_preorder V x;
  replace F_preorder := Set.mem_setOf_eq.mp F_preorder;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . exact finestFiltrationTransitiveClosureModel.isPreorder;
⟩

end Hilbert.S4.Kripke

end LO.Modal
