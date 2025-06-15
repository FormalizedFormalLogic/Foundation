import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.symm_preorder : FrameClass := { F | IsEquiv _ F.Rel }
abbrev Kripke.FrameClass.finite_symm_preorder: FrameClass := { F | Finite F.World ∧ IsEquiv _ F.Rel }

namespace Hilbert.KT4B.Kripke

instance sound : Sound (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KT4B) := consistent_of_sound_frameclass Kripke.FrameClass.symm_preorder $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KT4B) Kripke.FrameClass.symm_preorder := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.KT4B) Kripke.FrameClass.finite_symm_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_equiv V x;
  replace F_equiv := Set.mem_setOf_eq.mp F_equiv;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . exact finestFiltrationTransitiveClosureModel.isEquiv;
⟩

end Hilbert.KT4B.Kripke

lemma Logic.KT4B.Kripke.symm_preorder : Logic.KT4B = FrameClass.symm_preorder.logic := eq_hilbert_logic_frameClass_logic


end LO.Modal
