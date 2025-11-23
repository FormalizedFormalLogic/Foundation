import Foundation.Propositional.Hilbert.Corsi.Basic
import Foundation.Propositional.Hilbert.VCorsi.Basic

namespace LO.Propositional

open Entailment.Corsi

def weakerThan_VCorsi_Corsi_of_provable_axiomInstances (h : (Hilbert.Corsi Ax₂) ⊢* Ax₁.instances) : (Hilbert.VCorsi Ax₁) ⪯ (Hilbert.Corsi Ax₂) := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.VCorsi.rec! with
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
    | apply axiomC;
    | apply efq;
    | grind;

end LO.Propositional
