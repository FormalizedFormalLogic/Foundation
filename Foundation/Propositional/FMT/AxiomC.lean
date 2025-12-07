import Foundation.Propositional.FMT.Basic
import Foundation.Propositional.FMT.Completeness

namespace LO.Propositional.FMT

variable {F : Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomC (F : Frame) : Prop where
  collapse_ant : ∀ {x y : F.World} {φ ψ}, x ≺[φ ➝ ψ] y ↔ x ≺[φ] y
export HasAxiomC (collapse_ant)
attribute [grind =] collapse_ant

class HasAxiomD (F : Frame) : Prop where
  collapse_csq : ∀ {x y : F.World} {φ ψ}, x ≺[φ ➝ ψ] y ↔ x ≺[ψ] y
export HasAxiomD (collapse_csq)
attribute [grind =] collapse_csq

end Frame

lemma valid_axiomC_of_hasAxiomC [F.HasAxiomC] : F ⊧ Axioms.C φ ψ χ := by grind;
lemma valid_axiomD_of_hasAxiomD [F.HasAxiomD] : F ⊧ Axioms.D φ ψ χ := by grind;

instance [Entailment.F L] [Entailment.HasAxiomC L] [Entailment.Consistent L] [Entailment.Disjunctive L] : Frame.HasAxiomC (HintikkaModel L φ).toFrame where
  collapse_ant := by
    intro X Y ψ χ;
    dsimp [HintikkaModel, Frame.Rel']
    constructor;
    . intro h;
      match ψ with
      | ψ₁ ⋏ ψ₂ | ψ₁ ⋎ ψ₂ | ⊥ | #a => grind;
      | ψ₁ ➝ ψ₂ =>
        simp;
        sorry
    . intro h;
      match ψ with
      | ψ₁ ⋏ ψ₂ | ψ₁ ⋎ ψ₂ | ⊥ | #a =>
        sorry;
      | ψ₁ ➝ ψ₂ =>
        intro h₂;
        rcases @h (by grind) with h | h | h;
        . sorry;
        . sorry;
        . sorry;

end LO.Propositional.FMT
