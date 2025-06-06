import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomFourN
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Relation.Iterate


namespace LO.Modal

open Kripke
open Hilbert.Kripke
open IsGeachConfluent

namespace Kripke

protected abbrev FrameClass.weak_trans (n : ℕ+) : FrameClass := { F | IsWeakTrans n _ F.Rel }

end Kripke

namespace Hilbert.K4n.Kripke

variable {n : ℕ+}

instance sound : Sound (Hilbert.K4n n) (Kripke.FrameClass.weak_trans n) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  apply @validate_axiomFourN_of_weak_transitive n F F_trans;

instance consistent : Entailment.Consistent (Hilbert.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.weak_trans n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;> { simp [WeakTransitive]; tauto; }

instance canonical : Canonical (Hilbert.K4n n) (FrameClass.weak_trans n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K4n n) (FrameClass.weak_trans n) := inferInstance

end Hilbert.K4n.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma K4n.Kripke.eq_weak_trans_logic (n : ℕ+) : Logic.K4n n = (Kripke.FrameClass.weak_trans n).logic := eq_hilbert_logic_frameClass_logic

end Logic

end LO.Modal
