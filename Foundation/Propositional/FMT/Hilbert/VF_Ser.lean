module

public import Foundation.Propositional.FMT.Axiom.Ser

@[expose] public section

namespace LO.Propositional

open FMT

namespace FMT

instance : trivialFrame.IsNTSerial where
  nt_serial := by tauto;

end FMT


namespace HilbertVF.VF_Ser

open HilbertVF.FMT
open Formula.FMT

instance soundFMT : Sound HilbertVF.VF_Ser ({ F | F.IsNTSerial } : FMT.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ rfl F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomSer_of_isDNFSerial;

instance : Entailment.Consistent (HilbertVF.VF_Ser : HilbertVF ℕ) := consistent_of_sound_frameclass ({ F | F.IsNTSerial } : FMT.FrameClass) $ by
  use FMT.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance completeFMT : Complete HilbertVF.VF_Ser ({ F | F.IsNTSerial } : FMT.FrameClass) := by
  constructor;
  intro φ h;
  apply FMT.provable_of_validOnHintikkaModel;
  apply h;
  apply isDNFSerial_HintikkaModel;

end HilbertVF.VF_Ser

open Formula.FMT in
open Entailment.Corsi in
instance : (HilbertVF.VF : HilbertVF ℕ) ⪱ HilbertVF.VF_Ser := by
  constructor;
  . apply HilbertVF.weakerThan_of_le;
    tauto;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Ser;
    constructor;
    . simp;
    . apply HilbertVF.VF.soundFMT.not_provable_of_countermodel;
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
        grind;

end LO.Propositional

end
