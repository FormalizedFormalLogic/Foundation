import Foundation.Propositional.Kripke2.Hilbert
import Foundation.Propositional.Kripke2.FTheory
import Foundation.Propositional.Hilbert.F.Disjunctive

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

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F FrameClass.F := by
  apply instFrameClassSound;
  constructor;
  tauto;

instance : Entailment.Consistent Propositional.F := consistent_of_sound_frameclass FrameClass.F $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

instance Kripke2.complete : Complete Propositional.F FrameClass.F := by
  constructor;
  intro φ hφ;
  apply Kripke2.provable_of_validOncanonicalModel;
  apply hφ;
  tauto;

open Formula.Kripke2 in
lemma unprovable_noncontradiction : (Propositional.F ⊬ ∼((.atom 0) ⋏ ∼(.atom 0))) := by
  apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F);
  apply Kripke2.not_validOnFrameClass_of_exists_frame;
  use ⟨Fin 2, (λ x y => x = 0), 0, by omega⟩;
  constructor;
  . tauto;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ _ _ => True), 0;
    simp [Satisfies, Frame.Rel'];

end F



end LO.Propositional
