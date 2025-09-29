import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Filtration

@[simp]
lemma Set.inter_eq_univ {s t : Set α} : s ∩ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ := by
  simpa using @Set.sInter_eq_univ _ {s, t};

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsTransitive := by
  constructor;
  simp [Frame.box];

@[reducible] protected alias Frame.IsE4 := Frame.IsTransitive
protected class Frame.IsFiniteE4 (F : Frame) extends F.IsE4, F.IsFinite

protected abbrev FrameClass.E4 : FrameClass := { F | F.IsE4 }
protected abbrev FrameClass.finite_E4 : FrameClass := { F | F.IsFiniteE4 }


section

abbrev Frame.trivial_nontransitive : Frame := ⟨
  Fin 2,
  λ w =>
    match w with
    | 0 => ∅
    | 1 => {Set.univ}
⟩

instance : Frame.trivial_nontransitive.IsRegular := by
  constructor;
  rintro X Y x ⟨hx, hy⟩;
  match x with | 0 | 1 => simp_all;

instance : Frame.trivial_nontransitive.IsMonotonic := by
  constructor;
  rintro X Y x; match x with | 0 | 1 => simp

instance : Frame.trivial_nontransitive.IsReflexive := by
  constructor;
  rintro X x; match x with | 0 | 1 => first | tauto_set | simp_all;

@[simp]
lemma Frame.trivial_nontransitive.not_transitive : ¬Frame.trivial_nontransitive.IsTransitive := by
  by_contra hC;
  have := @(hC.trans Set.univ);
  have := @this 1 ?_;
  . have := Set.Subset.antisymm_iff.mp this |>.2;
    have := @this 0;
    simp at this;
  . simp [Frame.box];

@[simp]
lemma Frame.trivial_nontransitive.not_valid_axiomFour : ¬Frame.trivial_nontransitive ⊧ Axioms.Four (.atom 0) := by
  apply not_imp_not.mpr isTransitive_of_valid_axiomFour;
  simp;

end

end Neighborhood

namespace E4

instance : Sound Modal.E4 FrameClass.E4 := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFour_of_isTransitive;

instance : Entailment.Consistent Modal.E4 := consistent_of_sound_frameclass FrameClass.E4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.E4 FrameClass.E4 := minimalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Complete Modal.E4 FrameClass.finite_E4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.E4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
  };
⟩

end E4

instance : Modal.E ⪱ Modal.E4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.trivial_nontransitive;
      simp;

end LO.Modal
