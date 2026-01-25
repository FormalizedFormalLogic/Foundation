module

public import Foundation.Modal.Neighborhood.Logic.E4
public import Foundation.Modal.Neighborhood.Logic.ET
public import Foundation.Modal.Neighborhood.Logic.EN

@[expose] public section

namespace LO.Modal

instance {φ : Formula ℕ} : FormulaSet.IsSubformulaClosed (SetLike.coe (φ.subformulas ∪ (□⊤ : Formula ℕ).subformulas)) := by
  constructor;
  simp_all only [Finset.coe_union];
  rintro ψ (hψ | hψ);
  . intro ξ hξ;
    left;
    apply Formula.subformulas.subset_of_mem hψ;
    simpa;
  . intro ξ hξ;
    right;
    simp only [SetLike.mem_coe] at hψ;
    apply Formula.subformulas.subset_of_mem hψ;
    simpa;

open LO.Entailment
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEN4 (F : Frame) extends F.ContainsUnit, F.IsTransitive where
protected abbrev FrameClass.EN4 : FrameClass := { F | F.IsEN4 }

protected class Frame.IsFiniteEN4 (F : Frame) extends F.IsEN4, F.IsFinite where
protected abbrev FrameClass.finite_EN4 : FrameClass := { F | F.IsFiniteEN4 }

instance : counterframe_2_3_5.IsEN where
  contains_unit := by simp [Frame.box];


end Neighborhood


namespace EN4

instance Neighborhood.sound : Sound Modal.EN4 FrameClass.EN4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F hF <;>
  . have := Set.mem_setOf_eq.mp hF;
    simp;

instance consistent : Entailment.Consistent Modal.EN4 := consistent_of_sound_frameclass FrameClass.EN4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.complete : Complete Modal.EN4 FrameClass.EN4 := (basicCanonicity Modal.EN4).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  exact {}

/-- FFP of `Modal.EN4` -/
instance Neighborhood.finite_complete : Complete Modal.EN4 FrameClass.finite_EN4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.EN4);
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M (Finset.toSet $ φ.subformulas ∪ (□⊤ : Formula ℕ).subformulas) |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
    contains_unit := by
      apply transitiveFiltration.containsUnit (by simp) |>.contains_unit;
  };
⟩

end EN4

instance : Modal.EN ⪱ Modal.EN4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EN);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_2_3_5;
      constructor;
      . apply Set.mem_setOf_eq.mpr; infer_instance;
      . simp;

instance : Modal.E4 ⪱ Modal.EN4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E4);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . constructor;
        simp [Frame.box]
      . simp;

end LO.Modal
end
