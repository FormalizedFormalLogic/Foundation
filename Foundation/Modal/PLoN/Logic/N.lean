module

public import Foundation.Modal.PLoN.Hilbert
public import Foundation.Modal.PLoN.Completeness
public import Foundation.Modal.Hilbert.WithRE.Basic

@[expose] public section

namespace LO.Modal

open PLoN
open Formula.PLoN
open Hilbert.PLoN
open Modal.Entailment

namespace PLoN

abbrev AllFrameClass : PLoN.FrameClass := Set.univ

end PLoN


namespace N

instance PLoN.sound : Sound Modal.N PLoN.AllFrameClass := instFrameClassSound $ by
  constructor;
  grind;

instance : Entailment.Consistent Modal.N := consistent_of_nonempty_frameClass PLoN.AllFrameClass $ by
  use PLoN.terminalFrame;
  tauto;

instance PLoN.complete : Complete Modal.N PLoN.AllFrameClass := instComplete_of_mem_canonicalFrame $ by
  tauto;

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
      apply not_validOnFrameClass_of_exists_model;
      use {
        World := Fin 2,
        Rel ξ x y := if ξ = ∼∼(.atom 0) then True else False,
        Valuation x a := x = 0
      };
      constructor;
      . tauto;
      . simp [Frame.Rel'];


instance : Modal.N ⪱ Modal.K := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.K (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := PLoN.AllFrameClass)
      apply not_validOnFrameClass_of_exists_model;
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
      . simp [Frame.Rel'];

end LO.Modal
end
