module
import Foundation.Propositional.Hilbert.F.Basic
import Foundation.Propositional.Logic.Slash


namespace LO.Propositional

variable {Ax : Axiom ℕ} {φ ψ χ : Formula ℕ} {s : Substitution ℕ}

open Entailment.Corsi

instance Hilbert.F.instAczelSlashable (hs : ∀ {φ}, φ ∈ Ax → ∕ₐ[(Hilbert.F Ax)] φ) : (Hilbert.F Ax).AczelSlashable where
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
      induction h using F.rec! with
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
      | efq =>
        constructor;
        . exact efq;
        . tauto;
      | andIR ihφ ihψ => tauto;
      | axm => apply hs; assumption;

@[grind .] lemma slashable_axiomSer [Entailment.HasAxiomSer (Hilbert.F Ax)] : ∕ₐ[(Hilbert.F Ax)] ((Axioms.Ser)) := by grind
@[grind .] lemma slashable_axiomTra1 [Entailment.HasAxiomTra1 (Hilbert.F Ax)] : ∕ₐ[(Hilbert.F Ax)] ((Axioms.Tra1 φ ψ χ)) := by grind
@[grind .] lemma slashable_axiomRfl [Entailment.HasAxiomRfl (Hilbert.F Ax)] : ∕ₐ[(Hilbert.F Ax)] ((Axioms.Rfl φ ψ)) := by grind

@[grind .]
lemma slashable_propvar_axiomHrd (h : ∀ a, Hilbert.F Ax ⊢ #a ➝ ⊤ ➝ #a) : ∕ₐ[(Hilbert.F Ax)] (Axioms.Hrd #a) := by
  constructor;
  . apply h;
  . intro h;
    constructor;
    . apply af h;
    . grind;

instance F.AczelSlashable : Propositional.F.AczelSlashable := Hilbert.F.instAczelSlashable $ by tauto;
instance F.Disjunctive : Entailment.Disjunctive Propositional.F := inferInstance

instance F_Ser.AczelSlashable : Propositional.F_Ser.AczelSlashable := Hilbert.F.instAczelSlashable $ by grind;
instance F_Ser.Disjunctive : Entailment.Disjunctive Propositional.F_Ser := inferInstance

instance F_Rfl.AczelSlashable : Propositional.F_Rfl.AczelSlashable := Hilbert.F.instAczelSlashable $ by grind
instance F_Rfl.Disjunctive : Entailment.Disjunctive Propositional.F_Rfl := inferInstance

instance F_Tra1.AczelSlashable : Propositional.F_Tra1.AczelSlashable := Hilbert.F.instAczelSlashable $ by grind
instance F_Tra1.Disjunctive : Entailment.Disjunctive Propositional.F_Tra1 := inferInstance

instance F_Tra1_Hrd.AczelSlashable : Propositional.F_Tra1_Hrd.AczelSlashable := Hilbert.F.instAczelSlashable $ by
  rintro φ (⟨_, _, _, rfl⟩ | ⟨_, rfl⟩);
  . apply slashable_axiomTra1
  . apply slashable_propvar_axiomHrd;
    intro a;
    apply Hilbert.F.axm'!
    simp;
instance F_Tra1_Hrd.Disjunctive : Entailment.Disjunctive Propositional.F_Tra1_Hrd := inferInstance

instance F_Rfl_Tra1_Hrd.AczelSlashable : Propositional.F_Rfl_Tra1_Hrd.AczelSlashable := Hilbert.F.instAczelSlashable $ by
  rintro φ ((⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) | ⟨_, rfl⟩);
  . apply slashable_axiomRfl
  . apply slashable_axiomTra1
  . apply slashable_propvar_axiomHrd;
    intro a;
    apply Hilbert.F.axm'!
    simp;
instance F_Rfl_Tra1_Hrd.Disjunctive : Entailment.Disjunctive Propositional.F_Rfl_Tra1_Hrd := inferInstance

end LO.Propositional
