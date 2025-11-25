import Foundation.Propositional.Hilbert.Corsi.Basic
import Foundation.Propositional.Logic.Slash


namespace LO.Propositional

variable {α : Type*}
variable {Ax : Axiom α} {φ ψ : Formula α}

open Entailment.Corsi

instance Hilbert.Corsi.instAczelSlashable (hs : ∀ {φ s}, φ ∈ Ax → ∕ₐ[(Hilbert.Corsi Ax)] (φ⟦s⟧)) : (Hilbert.Corsi Ax).AczelSlashable where
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
      induction h using Corsi.rec! with
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
      | distributeAndOr =>
        constructor;
        . exact distributeAndOr;
        . rintro ⟨hφ, (hψ | hψ)⟩ <;> tauto;
      | axiomC =>
        constructor;
        . exact axiomC;
        . rintro ⟨⟨hφψ₁, hφψ₂⟩, ⟨hψχ₁, hψχ₂⟩⟩;
          constructor;
          . apply CK_of_C_of_C <;> assumption;
          . rintro h;
            constructor <;> grind;
      | axiomD =>
        constructor;
        . exact axiomD;
        . rintro ⟨⟨hφψ₁, hφψ₂⟩, ⟨hψχ₁, hψχ₂⟩⟩;
          constructor;
          . apply CA_of_C_of_C <;> assumption;
          . rintro (hφ | hψ) <;> grind;
      | axiomI =>
        constructor;
        . exact axiomI;
        . rintro ⟨⟨hφψ₁, hφψ₂⟩, ⟨hψχ₁, hψχ₂⟩⟩;
          constructor;
          . apply C_trans hφψ₁ hψχ₁;
          . grind;
      | impId =>
        constructor;
        . exact impId;
        . tauto;
      | mdp ihφψ ihφ => apply ihφψ.2 ihφ;
      | af ihφ =>
        constructor;
        . apply af;
          assumption;
        . tauto;
      | andIR ihφ ihψ => tauto;
      | axm => apply hs; assumption;

instance F.AczelSlashable : Propositional.F.AczelSlashable := Hilbert.Corsi.instAczelSlashable $ by tauto;
instance F.Disjunctive : Entailment.Disjunctive Propositional.F := inferInstance

instance F_Ser.AczelSlashable : Propositional.F_Ser.AczelSlashable := Hilbert.Corsi.instAczelSlashable $ by
  rintro φ s (rfl); grind;
instance F_Ser.Disjunctive : Entailment.Disjunctive Propositional.F := inferInstance


instance F_Rfl.AczelSlashable : Propositional.F_Rfl.AczelSlashable := Hilbert.Corsi.instAczelSlashable $ by
  rintro φ s (rfl); grind;
instance F_Rfl.Disjunctive : Entailment.Disjunctive Propositional.F := inferInstance


instance F_Tra1.AczelSlashable : Propositional.F_Tra1.AczelSlashable := Hilbert.Corsi.instAczelSlashable $ by
  rintro φ s (rfl); grind;
instance F_Tra1.Disjunctive : Entailment.Disjunctive Propositional.F_Tra1 := inferInstance

end LO.Propositional
