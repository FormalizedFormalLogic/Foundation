module

public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.Concatenation.Basic.Misc

@[expose] public section

namespace LO.FirstOrder.ConcatTheory

namespace Axiom

def concat_zero    : Sentence ℒ⌢ := “∀ x, x ⌢ 0 = x”
def zero_concat    : Sentence ℒ⌢ := “∀ x, 0 ⌢ x = 0”

def concat_assoc   : Sentence ℒ⌢ := “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”

def concat_ne_zero : Sentence ℒ⌢ := “∀ x y, x ⌢ y ≠ 0”

def concat_ne_one  : Sentence ℒ⌢ := “∀ x y, x ⌢ y ≠ 1”

def editor_axiom   : Sentence ℒ⌢ := “∀ x y u v, x ⌢ y = u ⌢ v → ∃ w, (u = x ⌢ w ∧ y = w ⌢ v) ∨ (x = u ⌢ w ∧ v = w ⌢ y)”

def nontrivial     : Sentence ℒ⌢ := “0 ≠ 1”

end Axiom

end LO.FirstOrder.ConcatTheory
