import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomB
import Foundation.Modal.Neighborhood.Logic.END4
import Foundation.Modal.Neighborhood.Logic.ET4
import Foundation.Modal.Neighborhood.Logic.ET
import Foundation.Modal.Neighborhood.Logic.E5
import Foundation.Vorspiel.Set.Fin

@[simp]
lemma Set.ne_univ_empty [Nonempty α] : Set.univ (α := α) ≠ ∅ := by simp only [ne_eq,
  univ_eq_empty_iff, not_isEmpty_of_nonempty, not_false_eq_true];

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

protected class Frame.IsET5 (F : Frame) extends F.IsReflexive, F.IsEuclidean
protected abbrev FrameClass.ET5 : FrameClass := { F | F.IsET5 }

variable {F : Frame}

instance : Frame.simple_blackhole.IsET5 where
  eucl := by
    intro X x hx;
    simp_all [Frame.simple_blackhole, Frame.box];

instance : counterframe_axiomFive.IsReflexive := by
  constructor;
  intro X x hx;
  simp_all [Frame.box];

section

variable [Entailment (Formula ℕ) S] {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.ET5 𝓢]

instance: (minimalCanonicity 𝓢).toModel.IsEuclidean := by
  apply Canonicity.isEuclidean;
  intro A X X_np;
  replace : {B | X ∉ (minimalCanonicity 𝓢).𝒩 B} = proofset 𝓢 ⊤ := by
    suffices ∀ B, X ∉ (minimalCanonicity 𝓢).𝒩 B by simpa [Set.eq_univ_iff_forall];
    rintro _ ⟨φ, _, hφ₂⟩;
    apply X_np;
    apply hφ₂;
  rw [this];
  apply minimalCanonicity 𝓢 |>.def_𝒩 A ⊤ |>.mp;
  apply MaximalConsistentSet.mem_of_prove;
  simp;

instance : (minimalCanonicity 𝓢).toModel.IsET5 where

end

abbrev counterframe_EN4_ENT4 : Neighborhood.Frame := ⟨Fin 2, λ x => {{x}, {x}ᶜ, Set.univ}⟩

@[simp]
lemma counterframe_2_3_5.not_valid_axiomT : ¬counterframe_2_3_5 ⊧ Axioms.T (Formula.atom a) := by
  apply not_imp_not.mpr isReflexive_of_valid_axiomT;
  by_contra! hC;
  have := hC.refl {0};
  have := @this 1
  simp at this;

end Neighborhood


namespace ET5

instance : Sound Modal.ET5 FrameClass.ET5 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.ET5 := consistent_of_sound_frameclass FrameClass.ET5 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.ET5 FrameClass.ET5 := (minimalCanonicity Modal.ET5).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ET5


instance : Modal.END ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.END);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_2_3_5;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        have := hC.refl {0};
        have := @this 1
        simp at this;

instance : Modal.ET ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ET);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ x => {{x}}⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance
      . simp;

instance : Modal.E5 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E5);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ _ => Set.univ⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
        . intro X x hx;
          simp_all [Frame.box, Frame.dia];
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        have : ∀ (y : Fin 2), y = 1 := by simpa using hC.refl {1};
        have := this 0;
        contradiction;

end LO.Modal
