import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Hilbert.K.Kripke

instance sound : Sound (Hilbert.K) FrameClass.all := instSound_of_validates_axioms FrameClass.all.validates_axiomK

instance sound_finite : Sound (Hilbert.K) FrameClass.finite_all := instSound_of_validates_axioms FrameClass.finite_all.validates_axiomK

instance : Entailment.Consistent (Hilbert.K) := consistent_of_sound_frameclass FrameClass.all (by simp)

instance : Kripke.Canonical (Hilbert.K) FrameClass.all := ⟨by trivial⟩

/-- Hilbert system for `K` is complete for class of all Kripke frame -/
instance complete : Complete (Hilbert.K) FrameClass.all := inferInstance

instance complete_finite : Complete (Hilbert.K) (FrameClass.finite_all) := ⟨by
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

end Hilbert.K.Kripke


namespace Logic

lemma K.Kripke.all : Logic.K = FrameClass.all.logic := eq_hilbert_logic_frameClass_logic
lemma K.Kripke.finite_all : Logic.K = FrameClass.finite_all.logic := eq_hilbert_logic_frameClass_logic

theorem K.proper_extension_of_Empty : Logic.Empty ⊂ Logic.K := by
  constructor;
  . simp;
  . suffices ∃ φ, Hilbert.K ⊢! φ by tauto_set;
    use ⊤;
    simp;

end Logic

end LO.Modal
