import Foundation.Propositional.FMT.Logic.VF

namespace LO.Propositional

namespace FMT

variable {F : FMT.Frame} {M : FMT.Model} {Γ : FormulaSet ℕ} {φ ψ χ : Formula ℕ}

namespace Frame

class IsDNFSerial (F : Frame) : Prop where
  dnf_serial : ∀ x : F, ∃ y, x ≺[∼∼⊥] y
export IsDNFSerial (dnf_serial)

end Frame

lemma valid_axiomSer_of_isDNFSerial [F.IsDNFSerial] : F ⊧ ∼∼⊤ := by
  intro V x y Rxy h₁;
  obtain ⟨z, Ryz⟩ := F.dnf_serial y;
  have : Formula.FMT.Forces (M := ⟨F, V⟩) z ⊥ := h₁ Ryz (by tauto);
  contradiction;

lemma isDNFSerial_of_valid_axiomSer (h : F ⊧ ∼∼⊤) : F.IsDNFSerial where
  dnf_serial := by
    intro x;
    simpa using @h (λ v a => True) F.root x F.rooted;

open ConsistentSaturatedHintikkaPair in
open Formula.FMT in
instance isDNFSerial_HintikkaModel {L}
  [Entailment.VF L] [Entailment.Disjunctive L] [Entailment.Consistent L]
  [Entailment.HasAxiomSer L]
  : (HintikkaModel L φ).toFrame.IsDNFSerial where
  dnf_serial := by
    intro x;
    obtain ⟨y, _, _⟩ := @ConsistentSaturatedHintikkaPair.lindenbaum (L := L) (φ := φ) _ ⟨x.1.1, x.1.2⟩ $ x.2.1;
    use y;
    intro hs;
    left;
    apply iff_mem₂_not_mem₁.mpr;
    by_contra hC;
    apply no_bot (H := y);
    apply imp_closed hs ?_ Entailment.Corsi.axiomSer;
    . grind;
    . exact Formula.subformulas.mem_imp hs |>.2;

end FMT


end LO.Propositional
