import Foundation.Propositional.Hilbert.Corsi.Basic
import Foundation.Propositional.Hilbert.VCorsi.Basic

namespace LO.Propositional

open Entailment.Corsi

variable [DecidableEq α] {Ax₁ Ax₂ : Axiom α}

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

def weakerThan_Corsi_VCorsi_of_provable_axiomInstances
  (h : (Hilbert.VCorsi Ax₂) ⊢* Ax₁.instances)
  (hD : ∀ φ ψ χ, (Hilbert.VCorsi Ax₂) ⊢ Axioms.D φ ψ χ)
  (hI : ∀ φ ψ χ, (Hilbert.VCorsi Ax₂) ⊢ Axioms.I φ ψ χ)
  : (Hilbert.Corsi Ax₁) ⪯ (Hilbert.VCorsi Ax₂) := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.Corsi.rec! with
  | axm => apply h; grind;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | axiomD => apply hD;
  | axiomI => apply hI;
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

instance : Propositional.VF_D_I ≊ Propositional.F := by
  apply Entailment.Equiv.antisymm;
  constructor;
  . apply weakerThan_VCorsi_Corsi_of_provable_axiomInstances;
    rintro _ hφ;
    dsimp at hφ;
    rcases hφ with ⟨_, (rfl | rfl), ⟨_, rfl⟩⟩ <;> simp;
  . apply weakerThan_Corsi_VCorsi_of_provable_axiomInstances;
    . rintro φ; simp;
    . intros; apply axiomD;
    . intros; apply axiomI;

end LO.Propositional
