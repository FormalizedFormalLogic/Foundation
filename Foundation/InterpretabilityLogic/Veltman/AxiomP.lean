module
import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomP (F : Frame) : Prop where
  S_P : ∀ {w x y z : F.World}, w ≺ x → x ≺ y → y ≺[w] z → y ≺[x] z
export HasAxiomP (S_P)

end Frame

@[simp high, grind .]
lemma validate_axiomP_of_HasAxiomP [F.HasAxiomP] : F ⊧ Axioms.P φ ψ := by
  intro V x h₁ y Rxy z Ryz h₂;
  obtain ⟨w, Sxyw, hw⟩ := h₁ z (F.trans Rxy Ryz) h₂;
  use w;
  constructor;
  . apply F.S_P Rxy Ryz Sxyw;
  . assumption;

lemma Frame.HasAxiomP.of_validate_axiomP (h : F ⊧ Axioms.P (.atom 0) (.atom 1)) : F.HasAxiomP := by
  constructor;
  intro w x y z Rwx Rxy Swyz;
  have := @h (λ u a => match a with | 0 => u = y | 1 => u = z | _ => False) w ?_ x Rwx y Rxy ?_;
  . obtain ⟨v, Sxyv, hv⟩ := this;
    apply hv ▸ Sxyv;
  . intro v Rwv hv;
    use z;
    constructor;
    . apply hv ▸ Swyz;
    . tauto;
  . tauto;

end LO.InterpretabilityLogic.Veltman
