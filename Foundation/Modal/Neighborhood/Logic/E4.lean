import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.E

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
  simp [Frame.box, Frame.box_iterate];

@[reducible] protected alias Frame.IsE4 := Frame.IsTransitive
protected abbrev FrameClass.E4 : FrameClass := { F | F.IsE4 }


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


namespace Hilbert

namespace E4.Neighborhood

instance : Sound Hilbert.E4 FrameClass.E4 := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFour_of_isTransitive;

instance : Entailment.Consistent Hilbert.E4 := consistent_of_sound_frameclass FrameClass.E4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end E4.Neighborhood

instance : Hilbert.E ⪱ Hilbert.E4 := by
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

end Hilbert

instance : 𝐄 ⪱ 𝐄𝟒 := inferInstance

end LO.Modal
