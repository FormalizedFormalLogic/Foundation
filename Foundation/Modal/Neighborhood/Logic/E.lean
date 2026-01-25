module

public import Foundation.Modal.Neighborhood.Hilbert
public import Foundation.Modal.Neighborhood.Completeness
public import Foundation.Modal.Neighborhood.Filtration
public import Foundation.Modal.Neighborhood.AxiomC
public import Foundation.Modal.Neighborhood.AxiomGeach
public import Foundation.Modal.Neighborhood.AxiomP
public import Foundation.Modal.Neighborhood.AxiomN


@[expose] public section

@[simp]
lemma Set.inter_eq_univ {s t : Set α} : s ∩ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ := by
  simpa using @Set.sInter_eq_univ _ {s, t};

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood


protected abbrev FrameClass.E : FrameClass := Set.univ

protected abbrev Frame.simple_whitehole : Frame := ⟨Unit, λ _ => ∅⟩

@[simp]
lemma Frame.simple_whitehole.not_valid_axiomN : ¬Frame.simple_whitehole ⊧ Axioms.N := by
  simp [Semantics.Models, ValidOnFrame, ValidOnModel, Satisfies];


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



namespace E

instance Neighborhood.sound : Sound Modal.E FrameClass.E := instSound_of_validates_axioms $ by simp;

instance consistent : Entailment.Consistent Modal.E := consistent_of_sound_frameclass FrameClass.E $ by
  use ⟨Unit, λ _ => {}⟩;
  simp;

instance Neighborhood.complete : Complete Modal.E FrameClass.E := (basicCanonicity Modal.E).completeness $ by tauto

end E


instance : Modal.E ⪱ Modal.EM := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
          match w with
          | 0 => {{1}}
          | 1 => {{0}, {0, 1}}
          | 2 => {{0}, {1, 2}},
        Val := λ w =>
          match w with
          | 0 => {0, 1}
          | 1 => {1, 2}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Models, Satisfies];
        grind;

instance : Modal.E ⪱ Modal.EC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.C (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {1}}
          | 1 => {∅},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Models, Satisfies];

instance : Modal.E ⪱ Modal.EN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . tauto;
      . simp;

instance : Modal.E ⪱ Modal.EM := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
          match w with
          | 0 => {{1}}
          | 1 => {{0}, {0, 1}}
          | 2 => {{0}, {1, 2}},
        Val := λ w =>
          match w with
          | 0 => {0, 1}
          | 1 => {1, 2}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Models, Satisfies];
        grind;

instance : Modal.E ⪱ Modal.EC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.C (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {1}}
          | 1 => {∅},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Models, Satisfies];

instance : Modal.E ⪱ Modal.EN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . tauto;
      . simp;

instance : Modal.E ⪱ Modal.EK := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.K (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {0, 1, 2}}
          | 1 => ∅
          | 2 => ∅,
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {0, 1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Models, Satisfies];
        constructor;
        . intro;
          grind;
        . tauto_set;

instance : Modal.E ⪱ Modal.ED := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ w => match w with | 0 => {{0}} | 1 => Set.univ⟩
      constructor;
      . tauto;
      . apply not_imp_not.mpr isSerial_of_valid_axiomD;
        by_contra! hC;
        have := @hC.serial {1} 1;
        simp [Frame.box, Frame.dia] at this;

instance : Modal.E ⪱ Modal.EP := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.P);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => {∅}⟩
      constructor;
      . tauto;
      . apply not_imp_not.mpr notContainsEmpty_of_valid_axiomP;
        by_contra! hC;
        simpa using hC.not_contains_empty;

instance : Modal.E ⪱ Modal.EB := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.B (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . tauto;
      . apply not_imp_not.mpr isSymmetric_of_valid_axiomB;
        by_contra! hC;
        have := hC.symm {()};
        simp [Frame.box] at this;

end LO.Modal
end
