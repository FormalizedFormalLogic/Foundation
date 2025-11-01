import Foundation.InterpretabilityLogic.Entailment.ILMinus

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J4 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4 𝓢

section

variable [Entailment.ILMinus_J4 𝓢]

-- TODO: Proposition 3.4 (⇒)
-- instance : HasAxiomJ4' 𝓢 := ⟨by sorry⟩

end


protected class ILMinus_J4' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4' 𝓢

section

variable [Entailment.ILMinus_J4' 𝓢]

-- TODO: Proposition 3.4 (⇐)
-- instance : HasAxiomJ4 𝓢 := ⟨by sorry⟩

end

-- TODO: Move to entailments
variable [Entailment.Minimal 𝓢] in
def C_trans₃ (h₁ : 𝓢 ⊢! φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢! χ ➝ ξ) : 𝓢 ⊢! φ ➝ ψ ➝ ξ := by
  apply deduct';
  apply deduct;
  exact (of h₂) ⨀ (deductInv $ deductInv' h₁);
variable [Entailment.Minimal 𝓢] in
lemma C_trans₃! (h₁ : 𝓢 ⊢ φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢ χ ➝ ξ) : 𝓢 ⊢ φ ➝ ψ ➝ ξ := ⟨C_trans₃ h₁.some h₂.some⟩


protected class ILMinus_J4Plus (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus 𝓢

section

variable [Entailment.ILMinus_J4Plus 𝓢]

instance : HasAxiomJ4' 𝓢 := ⟨by
  intro φ ψ;
  have : 𝓢 ⊢! (∼∼ψ ▷ ⊥) ➝ □(ψ ➝ ⊥) := C_trans CRhdNOL! $ box_regularity $ K_left negEquiv;
  have : 𝓢 ⊢! (ψ ▷ ⊥) ➝ □(ψ ➝ ⊥) := C_trans (R2! dni) this;
  apply C_swap $ C_trans this $ J4Plus!;
⟩

instance : HasAxiomJ4Plus' 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans (box_regularity CCC) $ J4Plus!;
⟩

end


protected class ILMinus_J4Plus' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus' 𝓢

section

variable [Entailment.ILMinus_J4Plus' 𝓢]

instance : HasAxiomJ4Plus'' 𝓢 := ⟨by
  intro A B C;
  dsimp only [Axioms.J4Plus''];
  -- apply C_trans $ J4Plus'! (𝓢 := 𝓢) (φ := A) (ψ := B) (χ := C);

  have H₁ : 𝓢 ⊢! C ▷ B ➝ C ▷ (A ➝ A ⋏ B) := R1! $ C_swap $ and₃;
  have H₂ : 𝓢 ⊢! □A ➝ (C ▷ (A ➝ B) ➝ C ▷ B) := J4Plus'!;

  sorry;
⟩

end


protected class ILMinus_J4Plus'' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus'' 𝓢

section

variable [Entailment.ILMinus_J4Plus'' 𝓢]

instance : HasAxiomJ4Plus 𝓢 := ⟨by
  intro φ ψ χ;
  have H₁ : 𝓢 ⊢! □(φ ➝ ψ) ➝ χ ▷ φ ➝ χ ▷ ((φ ➝ ψ) ⋏ φ) := J4Plus''!;
  have H₂ : 𝓢 ⊢! χ ▷ ((φ ➝ ψ) ⋏ φ) ➝ χ ▷ ψ := R1! $ C_trans (CKK _ _) $ innerMDP;
  exact C_trans₃ H₁ H₂;
⟩

end


end LO.InterpretabilityLogic.Entailment
