import Foundation.Propositional.FMT.Hilbert
import Foundation.Propositional.Hilbert.VCorsi.Disjunctive
import Foundation.Propositional.Hilbert.Corsi.Basic
import Foundation.Propositional.Hilbert.Corsi_VCorsi

namespace LO.Propositional

open FMT


namespace FMT

protected abbrev FrameClass.VF : FMT.FrameClass := Set.univ

abbrev trivialFrame : FMT.Frame where
  World := Unit
  Rel _ _ _ := True
  root := ()
  rooted := by simp

end FMT


namespace VF

open Hilbert.VCorsi.FMT

instance FMT.sound : Sound Propositional.VF FrameClass.VF := by
  apply instFrameClassSound;
  constructor;
  simp;

instance : Entailment.Consistent Propositional.VF := consistent_of_sound_frameclass FrameClass.VF $ by
  use FMT.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

open Formula.FMT in
lemma unprovable_axiomD : Propositional.VF ⊬ Axioms.D #0 #1 #2 := by
  apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.VF);
  apply FMT.not_validOnFrameClass_of_exists_frame;
  use {
    World := Fin 3,
    Rel := λ φ x y =>
      match φ, x, y with
      | _, 0, _ => True
      | φ, 1, 2 => φ = #0 ⋎ #1
      | _, _, _ => False
    ,
    root := 0,
    rooted := by tauto
  };
  constructor;
  . tauto;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use λ w a => match w, a with
      | 2, 2 => False
      | _, _ => True;
    use 0;
    apply Satisfies.not_def_imp.mpr;
    use 1;
    constructor;
    . tauto;
    . constructor;
      . constructor;
        . intro z; match z with | 0 | 1 | 2 => tauto
        . intro z; match z with | 0 | 1 | 2 => tauto
      . apply Satisfies.not_def_imp.mpr;
        use 2;
        tauto;

open Formula.FMT in
lemma unprovable_axiomI : Propositional.VF ⊬ Axioms.I #0 #1 #2 := by
  apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.VF);
  apply FMT.not_validOnFrameClass_of_exists_frame;
  use {
    World := Fin 3,
    Rel := λ φ x y =>
      match φ, x, y with
      | _, 0, _ => True
      | φ, 1, 2 => φ = #0
      | _, _, _ => False
    ,
    root := 0,
    rooted := by tauto
  };
  constructor;
  . tauto;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use λ w a => match w, a with
      | 2, 2 => False
      | _, _ => True;
    use 0;
    apply Satisfies.not_def_imp.mpr;
    use 1;
    refine ⟨?_, ?_, ?_⟩;
    . tauto;
    . constructor;
      . simp [Satisfies]
      . intro z R1z; match z with | 0 | 1 | 2 => grind;
    . apply Satisfies.not_def_imp.mpr;
      use 2;
      tauto;

end VF

end LO.Propositional
