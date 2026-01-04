import Foundation.Propositional.Hilbert.VF.Basic
import Foundation.Propositional.Logic.Slash


namespace LO.Propositional

variable {Ax : Axiom ℕ} {φ ψ χ : Formula ℕ} {s : Substitution ℕ}

open Entailment.Corsi

namespace Hilbert.VF

instance instAczelSlashable (hs : ∀ {φ}, φ ∈ Ax → ∕ₐ[(Hilbert.VF Ax)] φ) : (Hilbert.VF Ax).AczelSlashable where
  iff_ks_provable {φ} := by
    constructor;
    . intro h;
      induction φ with
      | hatom a => exact h;
      | hfalsum => contradiction;
      | hor φ ψ ihφ ihψ =>
        rcases h with h | h;
        . apply A_intro_left $ ihφ h;
        . apply A_intro_right $ ihψ h;
      | hand φ ψ ihφ ihψ => exact andIR (ihφ h.1) (ihψ h.2);
      | himp φ ψ ihφ ihψ => exact h.1;
    . intro h;
      induction h using VF.rec! with
      | orIntroL =>
        constructor;
        . exact orIntroL;
        . tauto;
      | orIntroR =>
        constructor;
        . exact orIntroR;
        . tauto;
      | andElimL =>
        constructor;
        . exact andElimL;
        . rintro ⟨_, _⟩; assumption;
      | andElimR =>
        constructor;
        . exact andElimR;
        . rintro ⟨_, _⟩; assumption;
      | impId =>
        constructor;
        . exact impId;
        . tauto;
      | distributeAndOr =>
        constructor;
        . exact distributeAndOr;
        . rintro ⟨hφ, (hψ | hψ)⟩ <;> tauto;
      | mdp ihφψ ihφ => apply ihφψ.2 ihφ;
      | af ihφ =>
        constructor;
        . apply af;
          assumption;
        . tauto;
      | efq =>
        constructor;
        . exact efq;
        . tauto;
      | ruleD ih₁ ih₂ =>
        constructor;
        . apply ruleD <;> assumption;
        . rintro (h | h) <;> grind;
      | ruleC ih₁ ih₂ =>
        constructor;
        . apply ruleC <;> assumption;
        . rintro h;
          constructor <;> grind;
      | ruleI ih₁ ih₂ =>
        constructor;
        . apply ruleI <;> assumption;
        . grind;
      | axm => apply hs; assumption;

@[grind .] lemma slashable_axiomSer [Entailment.HasAxiomSer (Hilbert.VF Ax)] : ∕ₐ[(Hilbert.VF Ax)] ((Axioms.Ser)) := by grind

end Hilbert.VF


instance VF.AczelSlashable : Propositional.VF.AczelSlashable := Hilbert.VF.instAczelSlashable $ by tauto;
instance VF.Disjunctive : Entailment.Disjunctive Propositional.VF := inferInstance

instance VF_Ser.AczelSlashable : Propositional.VF_Ser.AczelSlashable := Hilbert.VF.instAczelSlashable $ by grind;
instance VF_Ser.Disjunctive : Entailment.Disjunctive Propositional.VF_Ser := inferInstance

end LO.Propositional
