import Foundation.InterpretabilityLogic.Veltman.Hilbert

namespace LO.InterpretabilityLogic

open Veltman
open Formula.Veltman

namespace Veltman

protected abbrev FrameClass.CL : FrameClass := { F | F.IsCL }

abbrev trivialFrame : Veltman.Frame where
  toKripkeFrame := Modal.Kripke.blackpoint
  S _ _ _ := True

instance : Veltman.trivialFrame.IsCL where
  S_refl _ := ⟨by tauto⟩
  S_trans _ := ⟨by tauto⟩

lemma validates_CL_axioms_union {F : Veltman.Frame} [F.IsCL] : F ⊧* CL.axioms := by
  constructor;
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl);
  . apply ValidOnFrame.axiomK;
  . apply ValidOnFrame.axiomL;
  . apply ValidOnFrame.axiomJ1;
  . apply ValidOnFrame.axiomJ2;
  . apply ValidOnFrame.axiomJ3;
  . apply ValidOnFrame.axiomJ4;

end Veltman


namespace CL

instance Veltman.sound : Sound InterpretabilityLogic.CL FrameClass.CL := instSound_of_validates_axioms $ by
  constructor;
  intro φ hφ F hF;
  simp only [Set.mem_setOf_eq] at hF;
  apply validates_CL_axioms_union.models;
  assumption;

instance : Entailment.Consistent InterpretabilityLogic.CL := consistent_of_sound_frameclass FrameClass.CL $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end CL

end LO.InterpretabilityLogic
