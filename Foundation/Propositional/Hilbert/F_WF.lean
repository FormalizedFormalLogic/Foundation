module

public import Foundation.Propositional.Hilbert.F
public import Foundation.Propositional.Hilbert.WF

@[expose] public section

namespace LO.Propositional

open Entailment.Corsi

variable [DecidableEq α] {Ax₁ Ax₂ : Axiom α}

def weakerThan_WF_Corsi_of_provable_axioms (h : (Hilbert.F Ax₂) ⊢* Ax₁) : (Hilbert.WF Ax₁) ⪯ (Hilbert.F Ax₂) := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.WF.rec! with
  | axm => apply h; grind;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ =>
    first
    | apply impId;
    | apply andElimL;
    | apply andElimR;
    | apply orIntroL;
    | apply orIntroR;
    | apply distributeAndOr;
    | apply efq;
    | grind;

end LO.Propositional
end
