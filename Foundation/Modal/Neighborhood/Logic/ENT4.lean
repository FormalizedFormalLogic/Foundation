module

public import Foundation.Modal.Neighborhood.Logic.EN4
public import Foundation.Modal.Neighborhood.Logic.ET4

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsENT4 (F : Frame) extends F.ContainsUnit, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.ENT4 : FrameClass := { F | F.IsENT4 }

protected class Frame.IsFiniteENT4 (F : Frame) extends F.IsENT4, F.IsFinite where
protected abbrev FrameClass.finite_ENT4 : FrameClass := { F | F.IsFiniteENT4 }

abbrev counterframe_EN4_ENT4 : Neighborhood.Frame := ⟨Fin 2, λ x => {{x}, {x}ᶜ, Set.univ}⟩

instance : counterframe_EN4_ENT4.IsEN4 where
  contains_unit := by simp [Frame.box];
  trans := by
    rintro X x (rfl | rfl | rfl);
    . right; right;
      apply Set.eq_univ_iff_forall.mpr;
      intro y;
      match x, y with | 0, 0 | 0, 1 | 1, 0 | 1, 1 => simp;
    . right; right;
      apply Set.eq_univ_iff_forall.mpr;
      intro y;
      match x, y with | 0, 0 | 0, 1 | 1, 0 | 1, 1 => simp;
    . simp_all [Frame.box]

@[simp]
lemma counterframe_EN4_ENT4.not_valid_axiomT : ¬counterframe_EN4_ENT4 ⊧ Axioms.T (.atom 0) := by
  apply not_imp_not.mpr isReflexive_of_valid_axiomT;
  by_contra! hC;
  have := hC.refl {0};
  have := @this 1;
  simp [Frame.box] at this;

instance : Frame.simple_whitehole.IsET4 where
  refl := by simp [Frame.box];
  trans := by simp [Frame.box];

end Neighborhood


namespace ENT4

instance Neighborhood.sound : Sound Modal.ENT4 FrameClass.ENT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F hF <;>
  . have := Set.mem_setOf_eq.mp hF;
    simp;

instance consistent : Entailment.Consistent Modal.ENT4 := consistent_of_sound_frameclass FrameClass.ENT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance Neighborhood.complete : Complete Modal.ENT4 FrameClass.ENT4 := (basicCanonicity _).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  exact {}

instance Neighborhood.finite_complete : Complete Modal.ENT4 FrameClass.finite_ENT4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.ENT4);
  intro F hF V x;
  replace F_trans := Set.mem_setOf_eq.mp hF;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M (Finset.toSet $ φ.subformulas ∪ (□⊤ : Formula ℕ).subformulas) |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
    refl := by apply transitiveFiltration.isReflexive.refl;
    contains_unit := by apply transitiveFiltration.containsUnit (by simp) |>.contains_unit;
  };
⟩

end ENT4

instance : Modal.EN4 ⪱ Modal.ENT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EN4);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_EN4_ENT4;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance
      . simp;

instance : Modal.ET4 ⪱ Modal.ENT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    rintro _ (rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ET4);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . simp;

end LO.Modal
end
