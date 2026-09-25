module

public import Foundation.ProvabilityLogic.Classification.AD
public import Foundation.ProvabilityLogic.Classification.DS.Arithmetic

/-!
# Provability logics of trace `ω`

A provability logic of trace `ω` contained in `𝐒` is one of `𝐀`, `𝐃`, and `𝐒`.

## References

- [Bek90, Assertion 3]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/-- A provability logic of trace `ω` contained in `𝐒` is one of `𝐀`, `𝐃`, and `𝐒`.

- [Bek90, Assertion 3]
-/
theorem provabilityLogic_eq_A_or_eq_D_or_eq_S
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ)
    (hS : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo U : Logic α) = 𝐀 ∨
      (T.provabilityLogicRelativeTo U : Logic α) = 𝐃 ∨
      (T.provabilityLogicRelativeTo U : Logic α) = 𝐒 := by
  rcases (A_subset_provabilityLogic hT).eq_or_ssubset with h | h₁;
  · grind;
  rcases (D_subset_provabilityLogic hT h₁).eq_or_ssubset with h | h₂;
  · grind;
  · simp [hS.antisymm <| S_subset_provabilityLogic hT h₂];

end FFL.ProvabilityLogic

end
