import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.AxiomB
import Foundation.Modal.Neighborhood.Logic.END4
import Foundation.Modal.Neighborhood.Logic.ET4
import Foundation.Modal.Neighborhood.Logic.ET
import Foundation.Modal.Neighborhood.Logic.E5


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

instance [F.IsET5] : F.IsSymmetric where
  symm := by
    intro X x hx;
    apply F.eucl;
    apply F.refl_dual;
    assumption;

instance [F.IsET5] : F.IsTransitive where
  trans := by
    intro X x hx;
    have := @F.symm
    sorry;

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

lemma provable_axiomD : Modal.ET5 ⊢ Axioms.D φ := by
  suffices Modal.ET5 ⊢ Axioms.D (.atom 0) by apply Logic.subst (s := λ n => φ) this;
  apply Complete.complete (𝓜 := FrameClass.ET5);
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomD_of_isSerial;

noncomputable instance : Entailment.HasAxiomD Modal.ET5 := ⟨λ _ => provable_axiomD.some⟩


lemma provable_axiomFour : Modal.ET5 ⊢ Axioms.Four φ := by
  suffices Modal.ET5 ⊢ Axioms.Four (.atom 0) by apply Logic.subst (s := λ n => φ) this;
  apply Complete.complete (𝓜 := FrameClass.ET5);
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFour_of_isTransitive;

noncomputable instance : Entailment.HasAxiomFour Modal.ET5 := ⟨λ _ => provable_axiomFour.some⟩


lemma provable_axiomB : Modal.ET5 ⊢ Axioms.B φ := by
  suffices Modal.ET5 ⊢ Axioms.B (.atom 0) by apply Logic.subst (s := λ n => φ) this;
  apply Complete.complete (𝓜 := FrameClass.ET5);
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomB_of_isSymmetric;

noncomputable instance : Entailment.HasAxiomB Modal.ET5 := ⟨λ _ => provable_axiomB.some⟩

end ET5


instance : Modal.END4 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl | rfl) <;> simp;
  . sorry;

instance : Modal.ET ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . sorry;

instance : Modal.E5 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . sorry;

end LO.Modal
