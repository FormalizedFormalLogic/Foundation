module
import Foundation.Propositional.Kripke2.Logic.F_Tra1
import Foundation.Propositional.Kripke2.AxiomHrd

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected class Model.IsF_Tra1_Hrd (M : Kripke2.Model) extends M.IsTransitive, M.IsHereditary where
protected abbrev ModelClass.F_Tra1_Hrd : Kripke2.ModelClass := { M | M.IsF_Tra1_Hrd }

abbrev trivialModel : Kripke2.Model := ⟨trivialFrame, λ _ _ => True⟩

instance : trivialModel.IsF_Tra1_Hrd where
  hereditary := by tauto;

end Kripke2


namespace F_Tra1_Hrd

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Tra1_Hrd ModelClass.F_Tra1_Hrd := by
  apply instModelClassSound;
  constructor;
  rintro φ hφ M hM;
  replace hF := Set.mem_setOf_eq.mp hM;
  rcases hφ with (⟨_, _, _, rfl⟩ | ⟨_, rfl⟩);
  . apply valid_axiomTra₁_of_IsTransitive;
  . apply valid_axiomHrd_of_isHereditary;

instance : Entailment.Consistent Propositional.F_Tra1_Hrd := consistent_of_sound_modelclass ModelClass.F_Tra1_Hrd $ by
  use Kripke2.trivialModel;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Tra1_Hrd

instance : Propositional.F_Tra1 ⪱ Propositional.F_Tra1_Hrd := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Hrd #0);
    constructor;
    . apply Hilbert.F.axm'!;
      simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Tra1);
      apply Kripke2.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, (λ x y => x ≤ y), 0, by simp⟩, λ x _ => x = 0⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { trans := by omega; }
      . simp [Semantics.NotModels, Semantics.Models, Formula.Kripke2.Satisfies];
        omega;

end LO.Propositional
