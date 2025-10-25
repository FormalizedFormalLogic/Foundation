import Foundation.Modal.PLoN.Hilbert
import Foundation.Modal.PLoN.Completeness
import Foundation.Modal.Hilbert.WithRE.Basic

namespace LO.Modal

open PLoN
open Formula.PLoN
open Modal.Entailment

namespace PLoN

abbrev AllFrameClass : PLoN.FrameClass := Set.univ

instance : AllFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ _ => True⟩;
  tauto;

end PLoN


namespace N

instance : AllFrameClass.DefinedBy Modal.N.axioms.instances := ⟨by simp⟩

instance : Sound Modal.N PLoN.AllFrameClass := inferInstance

instance : Entailment.Consistent Modal.N := PLoN.Hilbert.consistent_of_FrameClass PLoN.AllFrameClass

instance : Canonical Modal.N PLoN.AllFrameClass := ⟨by tauto⟩

instance : Complete Modal.N PLoN.AllFrameClass := inferInstance

end N


instance : Modal.N ⪱ Modal.EN := by
  constructor;
  . suffices ∀ φ, Modal.N ⊢ φ → Modal.EN ⊢ φ by apply Logic.weakerThan_of_provable this;
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
          simpa [M, Semantics.Models, Formula.PLoN.ValidOnModel, Formula.PLoN.Satisfies] using this;
        constructor;
        . use 0;
          simp [M, PLoN.Frame.Rel'];
        . use 1;
          simp [M];


instance : Modal.N ⪱ Modal.K := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.K (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := PLoN.AllFrameClass)
      apply Formula.PLoN.ValidOnFrameClass.not_of_exists_model;
      use {
        World := Fin 2,
        Rel := λ ξ x y =>
          if ξ = (.atom 0) ➝ (.atom 1) then False
          else x < y
        Valuation :=
          λ w a =>
          match a with
          | 0 => w = 1
          | 1 => w = 0
          | _ => False,
      };
      constructor;
      . tauto;
      . simp only [ValidOnModel.iff_models, ValidOnModel, not_forall];
        use 0;
        apply Formula.PLoN.Satisfies.imp_def.not.mpr;
        push_neg;
        constructor;
        . intro x R0x;
          simp_all [Satisfies, Frame.Rel'];
        . apply Formula.PLoN.Satisfies.imp_def.not.mpr;
          push_neg;
          constructor;
          . intro x R0x;
            simp_all [Satisfies, Frame.Rel'];
            omega;
          . apply Satisfies.box_def.not.mpr;
            push_neg;
            use 1;
            constructor;
            . simp [Frame.Rel']
            . simp [Semantics.Models, Satisfies];

end LO.Modal
