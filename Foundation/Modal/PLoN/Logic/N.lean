import Foundation.Modal.PLoN.Hilbert
import Foundation.Modal.PLoN.Completeness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open PLoN
open Formula.PLoN

namespace PLoN

abbrev AllFrameClass : PLoN.FrameClass := Set.univ

instance : AllFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ _ => True⟩;
  tauto;

end PLoN

namespace Hilbert


namespace N

instance : AllFrameClass.DefinedBy Hilbert.N.axiomInstances := ⟨by simp_all [Hilbert.axiomInstances]⟩

instance : Entailment.Consistent Logic.N := PLoN.Hilbert.consistent_of_FrameClass PLoN.AllFrameClass

instance : Canonical Logic.N PLoN.AllFrameClass := ⟨by tauto⟩

instance : Complete Logic.N PLoN.AllFrameClass := inferInstance

end N

instance : Logic.N ⪱ Logic.K := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
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
            . simp [Semantics.Realize, Satisfies];

end Hilbert

end LO.Modal
