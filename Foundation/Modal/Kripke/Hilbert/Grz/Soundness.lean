import Foundation.Modal.Kripke.AxiomGrz

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev FrameClass.trans_wcwf : FrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ WeaklyConverseWellFounded F.Rel }
protected abbrev FrameClass.finite_strict_preorder: FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel }

namespace FrameClass.finite_strict_preorder

@[simp]
lemma nonempty : FrameClass.finite_strict_preorder.Nonempty := by
  use whitepoint;
  simp [Reflexive , Transitive, AntiSymmetric];
  infer_instance;

lemma validates_AxiomGrz : FrameClass.finite_strict_preorder.ValidatesFormula (Axioms.Grz (.atom 0)) := by
  simp [Validates];
  intro F;
  apply validate_AxiomGrz_of_finite_strict_preorder;

lemma validates_HilbertGrz : Kripke.FrameClass.finite_strict_preorder.Validates Hilbert.Grz.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomGrz;

end FrameClass.finite_strict_preorder

end Kripke

namespace Hilbert.Grz

instance Kripke.finite_sound : Sound (Hilbert.Grz) FrameClass.finite_strict_preorder :=
  instSound_of_validates_axioms FrameClass.finite_strict_preorder.validates_HilbertGrz

instance Kripke.consistent : Entailment.Consistent (Hilbert.Grz) :=
  consistent_of_sound_frameclass FrameClass.finite_strict_preorder (by simp)

end Hilbert.Grz

end LO.Modal
