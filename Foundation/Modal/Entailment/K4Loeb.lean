module

public import Foundation.Modal.Entailment.Basic

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

protected class K4Loeb (𝓢 : S) extends Entailment.K4 𝓢, LoebRule 𝓢

namespace K4Loeb

variable [Entailment.K4Loeb 𝓢]

protected def axiomL : 𝓢 ⊢! Axioms.L φ := by
  dsimp [Axioms.L];
  generalize e : □(□φ ➝ φ) ➝ □φ = ψ;
  have d₁ : [□(□φ ➝ φ), □ψ] ⊢[𝓢]! □□(□φ ➝ φ) ➝ □□φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₂ : [□(□φ ➝ φ), □ψ] ⊢[𝓢]! □□φ ➝ □φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₃ : 𝓢 ⊢! □(□φ ➝ φ) ➝ □□(□φ ➝ φ) := axiomFour;
  have : 𝓢 ⊢! □ψ ➝ ψ := by
    nth_rw 2 [←e]; apply deduct'; apply deduct;
    exact d₂ ⨀ (d₁ ⨀ ((of d₃) ⨀ (FiniteContext.byAxm)));
  exact loeb this;
instance : HasAxiomL 𝓢 := ⟨K4Loeb.axiomL⟩

end K4Loeb

end Entailment

end LO.Modal

end
