import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.Axioms

namespace LO.Modal

/-- `◇ᵏ□ˡp ⟶ □ᵐ◇ⁿq`   -/
def Geach' (p q : Formula α) : (k : ℕ) → (l : ℕ) → (m : ℕ) → (n : ℕ) → Formula α
  | 0,     0,     0,     0     => p ⟶ q
  | 0,     0,     m + 1, 0     => Geach' p (□q) 0 0 m 0
  | 0,     0,     m,     n + 1 => Geach' p (◇q) 0 0 m n
  | k + 1, 0,     m,     n     => Geach' (◇p) q k 0 m n
  | k,     l + 1, m,     n     => Geach' (□p) q k l m n

def Geach (p: Formula α) := Geach' p p

namespace Geach

variable (p : Formula α)

lemma AxiomT_def : AxiomT p = Geach p 0 1 0 0 := rfl
lemma AxiomB_def : AxiomB p = Geach p 0 0 1 1 := rfl
lemma AxiomD_def : AxiomD p = Geach p 0 1 0 1 := rfl
lemma Axiom4_def : Axiom4 p = Geach p 0 1 2 0 := rfl
lemma Axiom5_def : Axiom5 p = Geach p 1 0 1 1 := rfl
lemma AxiomDot2_def : AxiomDot2 p = Geach p 1 1 1 1 := rfl
lemma AxiomCD_def : AxiomCD p = Geach p 1 0 1 0 := rfl
lemma AxiomC4_def : AxiomC4 p = Geach p 0 2 1 0 := rfl

end Geach

end LO.Modal
