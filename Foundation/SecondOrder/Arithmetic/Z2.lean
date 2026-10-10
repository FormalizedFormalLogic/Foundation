module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.SecondOrder.Syntax.BinderNotation
public import Foundation.SecondOrder.LK.Basic

/-!
# Second-order arithmetic: $\mathsf{Z_2}$
-/

@[expose] public section

namespace FFL.SecondOrder

namespace Theory

def induction : Sentence ℒₒᵣ := s“∀² X, 0 ∈ X ∧ (∀ x, x ∈ X → x + 1 ∈ X) → ∀ x, x ∈ X”

/-! The second-order arithmetic. -/
def Z2 : Theory ℒₒᵣ := insert induction 𝗣𝗔⁻

notation "𝗭₂" => Z2

end Theory

end FFL.SecondOrder
