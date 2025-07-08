import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

@[reducible] protected alias FrameClass.K := FrameClass.all
@[reducible] protected alias FrameClass.finite_K := FrameClass.finite_all

end Kripke


namespace Hilbert.K.Kripke

instance : Sound (Hilbert.K) FrameClass.K := instSound_of_validates_axioms FrameClass.all.validates_axiomK

instance : Sound (Hilbert.K) FrameClass.finite_K := instSound_of_validates_axioms FrameClass.finite_all.validates_axiomK

instance : Entailment.Consistent (Hilbert.K) := consistent_of_sound_frameclass FrameClass.K (by simp)

instance : Kripke.Canonical (Hilbert.K) FrameClass.K := ⟨by trivial⟩

instance : Complete (Hilbert.K) FrameClass.K := inferInstance

instance : Complete (Hilbert.K) (FrameClass.finite_K) := ⟨by
  intro φ hp;
  apply Complete.complete (𝓜 := FrameClass.K);
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFiltrationModel M ↑φ.subformulas;
  apply filtration FM (coarsestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Frame.isFinite_iff _ |>.mpr
  apply FilterEqvQuotient.finite;
  simp;
⟩

end Hilbert.K.Kripke


lemma K.Kripke.eq_K : Modal.K = FrameClass.K.logic := eq_hilbert_logic_frameClass_logic
lemma K.Kripke.eq_finite_K : Modal.K = FrameClass.finite_K.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal
