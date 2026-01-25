module

public import Foundation.Propositional.Kripke2.Logic.F_Rfl_Tra1
public import Foundation.Propositional.Kripke2.Logic.F_Tra1_Hrd

@[expose] public section

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected class Model.IsF_Rfl_Tra1_Hrd (M : Kripke2.Model) extends M.IsReflexive, M.IsTransitive, M.IsHereditary where
protected abbrev ModelClass.F_Rfl_Tra1_Hrd : Kripke2.ModelClass := { M | M.IsF_Rfl_Tra1_Hrd }

instance : trivialModel.IsF_Rfl_Tra1_Hrd where

end Kripke2


namespace F_Rfl_Tra1_Hrd

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Rfl_Tra1_Hrd ModelClass.F_Rfl_Tra1_Hrd := by
  apply instModelClassSound;
  constructor;
  rintro φ hφ M hM;
  replace hF := Set.mem_setOf_eq.mp hM;
  rcases hφ with ((⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) | ⟨_, rfl⟩);
  . apply valid_axiomRfl_of_isReflexive;
  . apply valid_axiomTra₁_of_IsTransitive;
  . apply valid_axiomHrd_of_isHereditary;

instance : Entailment.Consistent Propositional.F_Rfl_Tra1_Hrd := consistent_of_sound_modelclass ModelClass.F_Rfl_Tra1_Hrd $ by
  use Kripke2.trivialModel;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Rfl_Tra1_Hrd

instance : Propositional.F_Tra1_Hrd ⪱ Propositional.F_Rfl_Tra1_Hrd := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . apply Hilbert.F.axm'!;
      simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.ModelClass.F_Tra1_Hrd);
      apply Kripke2.not_validOnModelClass_of_exists_model_world;
      use ⟨⟨Fin 2, (λ x y => x = 0), 0, by simp⟩, λ x a => a = 0⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega;
          hereditary := by tauto;
        }
      . simp [Semantics.NotModels, Semantics.Models, Formula.Kripke2.Satisfies];
        omega;

instance : Propositional.F_Rfl_Tra1 ⪱ Propositional.F_Rfl_Tra1_Hrd := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Hrd #0);
    constructor;
    . apply Hilbert.F.axm'!;
      simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Rfl_Tra1);
      apply Kripke2.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≤ y, 0, by simp⟩, λ x a => x = 0⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega;
          refl := by omega;
        }
      . simp [Semantics.NotModels, Semantics.Models, Formula.Kripke2.Satisfies];
        grind;

end LO.Propositional
end
