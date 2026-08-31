module

public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick

/-!
# Sigma-one definability and incompleteness
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open LO.Entailment

noncomputable instance (T : ArithmeticTheory) [T.«Σ₁»] [𝗥₀ ⪯ T] : 𝗥₀ ⪯ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))

noncomputable instance (T : ArithmeticTheory) [T.«Σ₁»] [𝗜𝚺₁ ⪯ T] : 𝗜𝚺₁ ⪯ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))

end LO.FirstOrder.Arithmetic
