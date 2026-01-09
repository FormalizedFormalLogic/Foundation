module
import Foundation.InterpretabilityLogic.Entailment.ILMinus

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILMinus_M (𝓢 : S) extends InterpretabilityLogic.Entailment.ILMinus 𝓢, HasAxiomM 𝓢

variable [Entailment.ILMinus_M 𝓢]

instance : HasAxiomKM1 𝓢 := ⟨by
  intro φ ψ;
  apply C_trans $ axiomM! (χ := ∼ψ);
  apply C_trans $ show 𝓢 ⊢! ((φ ⋏ □(∼ψ)) ▷ (◇ψ ⋏ □(∼ψ))) ➝ ((φ ⋏ □(∼ψ)) ▷ ⊥) by
    apply R1!;
    apply replace_CK_left IMNLN!;
    apply left_K_symm;
    apply CKNO;
  apply C_trans CRhdOLN!;
  apply box_regularity;
  apply C_trans CNKANN;
  apply left_A_intro;
  . apply CNC;
  . apply C_swap;
    apply deduct';
    apply of;
    apply INLNM!;
⟩

end LO.InterpretabilityLogic.Entailment
