import Foundation.Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

noncomputable section

open Classical

namespace LO.Arith

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def x : V := ⌜Arith.exponentialDef.val⌝

def y : V := ⌜remDef.val⌝

example : ![(x : V)] 0 = x := by simp -- no memory leaks.

example : ∀ x : V, ![x, x] 0 = x := by simp -- no memory leaks.

example : ![(x : V), x] 0 = x := by
  -- simp only [Matrix.cons_val_zero] -- memory leaks!
  sorry

example : ![(y : V), y] 0 = y := by
  -- simp -- no memory leaks, but takes time.
  sorry

end LO.Arith
