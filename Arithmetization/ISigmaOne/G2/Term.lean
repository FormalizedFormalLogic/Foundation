import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace FormalizedTerm

variable (M)

structure Language where
  Func (arity : M) : M → Prop
  Rel (arity : M) : M → Prop


/--  -/
structure FreeStruc where
  arity : M → M



/--

```lean
 M:       0 1 2 3 4  5  ...  3 + k   4 + k  5 + k ...
          : : : : :  :         :       :      :
 symbols: 0 1 + * #0 #1 ... #(k - 1)   &0     &1  ...
          : : : : :  :         :       :      :
 varity:  2 2 4 4 0  0  ...    0       1      1   ...
```
 -/
def Lor : FreeStruc M := ⟨fun x ↦ by {


 }⟩




lemma gen_exists (n T : M) :
  ∃! T' : M, ∀ x : M, x ∈ T' ↔
    (∃ v < n, x = ⟪0, ⟪0, v⟫⟫) ∨ -- variable
    (x = ⟪0, ⟪1, 0⟫⟫) ∨          -- constant 0
    (x = ⟪0, ⟪1, 0⟫⟫) ∨          -- constant 1
    (∃ t₁ ∈ T, ∃ t₂ ∈ T, x = ⟪2, ⟫)
     := by {  }


def gen (n T : M) : M := T


end FormalizedTerm


end LO.FirstOrder.Arith.Model

end
