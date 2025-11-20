import Foundation.Propositional.Kripke2.Hilbert


namespace LO.Propositional

open Kripke2


namespace Kripke2

protected abbrev FrameClass.F : Kripke2.FrameClass := Set.univ

abbrev trivialFrame : Kripke2.Frame where
  World := Unit
  Rel _ _ := True
  root := ()
  rooted := by simp

end Kripke2


namespace F

open Hilbert.Corsi.Kripke2

instance Kripke2.sound : Sound Propositional.F FrameClass.F := by
  apply instFrameClassSound;
  constructor;
  tauto;

instance : Entailment.Consistent Propositional.F := consistent_of_sound_frameclass FrameClass.F $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

end F


end LO.Propositional
