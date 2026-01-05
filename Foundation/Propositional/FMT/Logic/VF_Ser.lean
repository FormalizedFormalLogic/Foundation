import Foundation.Propositional.FMT.Logic.VF
import Foundation.Propositional.FMT.AxiomSer

namespace LO.Propositional

open FMT


namespace FMT

protected abbrev FrameClass.VF_Ser : FMT.FrameClass := { F | F.IsNTSerial }

instance : trivialFrame.IsNTSerial where
  nt_serial := by tauto;

end FMT


namespace VF_Ser

open Hilbert.VF.FMT
open Formula.FMT


instance FMT.sound : Sound Propositional.VF_Ser FrameClass.VF_Ser := by
  apply instFrameClassSound;
  constructor;
  rintro φ rfl F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomSer_of_isDNFSerial;

instance : Entailment.Consistent Propositional.VF_Ser := consistent_of_sound_frameclass FrameClass.VF_Ser $ by
  use FMT.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance FMT.complete : Complete Propositional.VF_Ser FrameClass.VF_Ser := by
  constructor;
  intro φ h;
  apply FMT.provable_of_validOnHintikkaModel;
  apply h;
  apply isDNFSerial_HintikkaModel;

open Formula.FMT

end VF_Ser

open Formula.FMT in
open Entailment.Corsi in
instance : Propositional.VF ⪱ Propositional.VF_Ser := by
  constructor;
  . apply Hilbert.VF.weakerThan_of_subset_axioms;
    tauto;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Ser;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FMT.FrameClass.VF);
      apply FMT.not_validOnFrameClass_of_exists_model_world;
      use {
        World := Fin 2,
        Rel φ x y := x = 0,
        root := 0,
        rooted := by grind;
        Val _ _ := True
      }, 0;
      constructor;
      . tauto;
      . apply Formula.FMT.Forces.not_def_imp.mpr;
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . tauto;
        . grind;
        . tauto;

end LO.Propositional
