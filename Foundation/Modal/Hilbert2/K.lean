import Foundation.Modal.Hilbert2.Basic

namespace LO.Modal.Hilbert

variable {H : Hilbert α}

open Deduction

section

class HasK (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hK : H.HasK] : System.HasAxiomK H where
  K φ ψ := by
    simpa [hK.ne_pq] using
      subst (s := λ b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b)) $
      maxm hK.mem_K;

end


section

protected def K : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩

instance : (Hilbert.K).HasK where
  p := 0
  q := 1
  ne_pq := by trivial;

instance : System.K (Hilbert.K) where

end

end LO.Modal.Hilbert
