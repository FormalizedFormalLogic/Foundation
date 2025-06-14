import Foundation.Modal.Hilbert.Basic

namespace LO.Modal

namespace Hilbert

variable {H : Hilbert α}

open Deduction

class HasK (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hK : H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    apply maxm;
    use Axioms.K (.atom hK.p) (.atom hK.q);
    constructor;
    . exact hK.mem_K;
    . use (λ b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b));
      simp [hK.ne_pq];

protected abbrev K : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩
instance : Hilbert.K.FiniteAxiomatizable where
instance : Hilbert.K.HasK where p := 0; q := 1
instance : Entailment.K (Hilbert.K) where

end Hilbert


protected abbrev Logic.K := Hilbert.K.logic

end LO.Modal
