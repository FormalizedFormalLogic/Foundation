module

public import Foundation.SecondOrder.Arithmetic.Z2
public import Foundation.SecondOrder.LK.RestrictedComprehension

/-!
# Theory $\mathsf{ACA_0}$

The structural rules are the standard local weakening and contraction rules.
-/

@[expose] public section

namespace FFL.SecondOrder

namespace TheoryRestrictedComprehension

/-! The fragment of second-order arithmetic with arithmetic comprehension. -/
def ACA0 : TheoryRestrictedComprehension ℒₒᵣ where
  theory := 𝗭₂
  comprehension := Semiformula.IsElementary

notation "𝗔𝗖𝗔₀" => ACA0

end TheoryRestrictedComprehension

end FFL.SecondOrder
