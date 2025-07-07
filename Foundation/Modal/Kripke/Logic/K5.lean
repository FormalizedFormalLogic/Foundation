import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

abbrev Frame.IsK5 (F : Frame) := F.IsEuclidean

abbrev FrameClass.K5 : FrameClass := { F | F.IsK5 }

end Kripke


namespace Logic.K5.Kripke

instance sound : Sound (Hilbert.K5) Kripke.FrameClass.K5 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_eucl _ rfl;
  exact validate_AxiomFive_of_euclidean (eucl := F_eucl);

instance consistent : Entailment.Consistent (Hilbert.K5) :=
  consistent_of_sound_frameclass Kripke.FrameClass.K5 $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance canonical : Canonical (Hilbert.K5) Kripke.FrameClass.K5 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K5) Kripke.FrameClass.K5 := inferInstance

lemma eucl : Logic.K5 = Kripke.FrameClass.K5.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K ⪱ Logic.K5 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K5 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      simpa [K.Kripke.all];
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x _ => x = 0⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), ¬x = 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;

end Logic.K5.Kripke

end LO.Modal
