import Foundation.IntProp.Hilbert2.Basic

namespace LO.IntProp.Hilbert

variable {H : Hilbert α}

open Deduction

section

class HasEFQ (H : Hilbert α) where
  p : α
  mem_efq : (⊥ ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hEfq : H.HasEFQ] : System.HasAxiomEFQ H where
  efq φ := by
    apply eaxm;
    use Axioms.EFQ (Formula.atom hEfq.p);
    constructor;
    . exact hEfq.mem_efq;
    . use (λ b => if hEfq.p = b then φ else (.atom b));
      simp;

end


section

protected abbrev Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩
instance : Hilbert.Int.FiniteAxiomatizable where
instance : Hilbert.Int.HasEFQ where p := 0;
instance : System.Intuitionistic (Hilbert.Int) where

end

end LO.IntProp.Hilbert
