import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

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

open finestFilterationTransitiveClosureModel in
instance finiteComplete : Complete (Hilbert.S4) Kripke.FrameClass.finite_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  rintro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, by sorry⟩;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.S4.Kripke

end LO.Modal
