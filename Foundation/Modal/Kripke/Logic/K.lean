import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Logic.K.Kripke

instance sound : Sound (Logic.K) FrameClass.all := instSound_of_validates_axioms FrameClass.all.validates_axiomK

instance sound_finite : Sound (Logic.K) FrameClass.finite_all := instSound_of_validates_axioms FrameClass.finite_all.validates_axiomK

instance : Entailment.Consistent (Logic.K) := consistent_of_sound_frameclass FrameClass.all (by simp)

instance : Kripke.Canonical (Logic.K) FrameClass.all := ⟨by trivial⟩

instance complete : Complete (Logic.K) FrameClass.all := inferInstance

instance complete_finite : Complete (Logic.K) (FrameClass.finite_all) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFiltrationModel M ↑φ.subformulas;
  apply filtration FM (coarsestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Frame.isFinite_iff _ |>.mpr
  apply FilterEqvQuotient.finite;
  simp;
⟩

lemma all : Logic.K = FrameClass.all.logic := eq_hilbert_logic_frameClass_logic
lemma finite_all : Logic.K = FrameClass.finite_all.logic := eq_hilbert_logic_frameClass_logic

end Logic.K.Kripke


end LO.Modal
