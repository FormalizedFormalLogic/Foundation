import Foundation.Propositional.FMT.Logic.VF

namespace LO.Propositional

namespace FMT

variable {F : FMT.Frame} {M : FMT.Model} {Γ : FormulaSet ℕ} {φ ψ χ : Formula ℕ}

namespace Frame

class IsNTSerial (F : Frame) : Prop where
  nt_serial : ∀ x : F, ∃ y, x ≺[∼⊤] y
export IsNTSerial (nt_serial)

end Frame

lemma valid_axiomSer_of_isDNFSerial [F.IsNTSerial] : F ⊧ ∼∼⊤ := by
  intro V x y Rxy h₁;
  obtain ⟨z, Ryz⟩ := F.nt_serial y;
  have : Formula.FMT.Forces (M := ⟨F, V⟩) z ⊥ := h₁ Ryz (by tauto);
  contradiction;

lemma isDNFSerial_of_valid_axiomSer (h : F ⊧ ∼⊤) : F.IsNTSerial where
  nt_serial := by
    intro x;
    simpa using @h (λ v a => True) F.root x F.rooted;

lemma valid_axiomO_f (h : F ⊧ ∼⊤) : F ⊧ ∼∼⊤ := by
  haveI := isDNFSerial_of_valid_axiomSer h;
  apply valid_axiomSer_of_isDNFSerial;

open ConsistentSaturatedHintikkaPair in
open Formula.FMT in
instance isDNFSerial_HintikkaModel {L}
  [Entailment.VF L] [Entailment.Disjunctive L] [Entailment.Consistent L]
  [Entailment.HasAxiomSer L]
  : (HintikkaModel L φ).toFrame.IsNTSerial where
  nt_serial := by
    intro x;
    use x;
    intro hs;
    left;
    apply iff_mem₂_not_mem₁.mpr;
    by_contra hC;
    apply no_bot (H := x);
    apply imp_closed hs ?_ Entailment.Corsi.axiomSer;
    . grind;
    . grind;

end FMT


end LO.Propositional
