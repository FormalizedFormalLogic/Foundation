import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

namespace Kripke

abbrev FrameClass.trans_cwf : FrameClass := { F | Transitive F.Rel ∧ ConverseWellFounded F.Rel }

abbrev FrameClass.finite_trans_irrefl: FrameClass := { F | F.IsFinite ∧ Transitive F.Rel ∧ Irreflexive F.Rel }

namespace FrameClass.finite_trans_irrefl

@[simp]
lemma nonempty : FrameClass.finite_trans_irrefl.Nonempty := by
  use blackpoint;
  simp [Irreflexive, Transitive];
  infer_instance;

lemma validates_AxiomL : FrameClass.finite_trans_irrefl.ValidatesFormula (Axioms.L (.atom 0)) := by
  simp [Validates];
  intro F;
  apply validate_AxiomL_of_finite_trans_irrefl;

lemma validates_HilbertGL : Kripke.FrameClass.finite_trans_irrefl.Validates Hilbert.GL.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomL;

end FrameClass.finite_trans_irrefl

end Kripke


namespace Hilbert.GL

instance Kripke.finite_sound : Sound (Hilbert.GL) FrameClass.finite_trans_irrefl :=
  instSound_of_validates_axioms FrameClass.finite_trans_irrefl.validates_HilbertGL

instance Kripke.consistent : Entailment.Consistent (Hilbert.GL) :=
  consistent_of_sound_frameclass FrameClass.finite_trans_irrefl (by simp)

end Hilbert.GL

end LO.Modal
