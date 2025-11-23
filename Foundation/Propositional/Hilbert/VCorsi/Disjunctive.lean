import Foundation.Propositional.Hilbert.VCorsi.Basic
import Foundation.Propositional.Logic.KleeneSlash


namespace LO.Propositional

variable {α : Type*}
variable {Ax : Axiom α} {φ ψ : Formula α}

open Entailment.Corsi

instance Hilbert.VCorsi.instKleeneSlashable (hs : ∀ {φ s}, φ ∈ Ax → ∕[(Hilbert.VCorsi Ax)] (φ⟦s⟧)) : (Hilbert.VCorsi Ax).KleeneSlashable where
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
      induction h using VCorsi.rec! with
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
      | dilemma ih₁ ih₂ =>
        constructor;
        . apply dilemma <;> assumption;
        . rintro (h | h) <;> grind;
      | greedy ih₁ ih₂ =>
        constructor;
        . apply greedy <;> assumption;
        . rintro h;
          constructor <;> grind;
      | axm => apply hs; assumption;


instance VF.KleeneSlashable : Propositional.VF.KleeneSlashable := Hilbert.VCorsi.instKleeneSlashable $ by tauto;
instance VF.Disjunctive : Entailment.Disjunctive Propositional.VF := inferInstance


end LO.Propositional
