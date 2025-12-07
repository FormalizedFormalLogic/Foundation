import Foundation.Propositional.Hilbert.WF.Basic
import Foundation.Propositional.Hilbert.VF.Basic

namespace LO.Propositional

open Entailment.Corsi

variable [DecidableEq α] {Ax₁ Ax₂ : Axiom α}

def weakerThan_WF_VF_of_provable_axioms (h : (Hilbert.WF Ax₂) ⊢* Ax₁) : (Hilbert.VF Ax₁) ⪯ (Hilbert.WF Ax₂) := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.VF.rec! with
  | axm => apply h; grind;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ =>
    first
    | apply impId;
    | apply andElimL;
    | apply andElimR;
    | apply orIntroL;
    | apply orIntroR;
    | apply collectOrAnd;
    | apply efq;
    | grind;

end LO.Propositional
