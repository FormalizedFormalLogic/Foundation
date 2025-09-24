import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.PLoN.Logic.N

namespace LO.Modal

open Formula (atom)
open Entailment
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEN := Frame.ContainsUnit
protected abbrev FrameClass.EN : FrameClass := { F | F.IsEN }

end Neighborhood




instance : Sound Modal.EN FrameClass.EN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F hF;
  simp_all;

instance : Entailment.Consistent Modal.EN := consistent_of_sound_frameclass FrameClass.EN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.EN FrameClass.EN := minimalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Modal.E ⪱ Modal.EN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 1,
        𝒩 := λ w => ∅,
        Val := λ w => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];



instance : Modal.N ⪱ Modal.EN := by

  constructor;
  . suffices ∀ φ, Modal.N ⊢! φ → Modal.EN ⊢! φ by apply Logic.weakerThan_of_provable this;
    intro φ hφ;
    induction hφ using Hilbert.Normal.rec! with
    | axm s h => simp at h;
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | _ => simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use □(.atom 0) ⭤ □(∼∼.atom 0);
    constructor;
    . apply re!;
      cl_prover;
    . apply Sound.not_provable_of_countermodel (𝓜 := PLoN.AllFrameClass);
      apply Formula.PLoN.ValidOnFrameClass.not_of_exists_model;
      let M : PLoN.Model := {
        World := Fin 2,
        Rel ξ x y := if ξ = ∼∼(.atom 0) then True else False,
        Valuation x a := x = 0
      };
      use M;
      constructor;
      . tauto;
      . suffices (∃ x : M.World, ∀ y : M.World, (PLoN.Frame.Rel' (.atom 0) x y) → y = 0) ∧ ∃ x : M.World, x ≠ 0 by
          simpa [M, Semantics.Realize, Formula.PLoN.ValidOnModel, Formula.PLoN.Satisfies] using this;
        constructor;
        . use 0;
          simp [M, PLoN.Frame.Rel'];
        . use 1;
          simp [M];

end LO.Modal
