import Foundation.Modal.Hilbert.Basic

namespace LO.Modal

namespace Hilbert

variable {α} [DecidableEq α] {H : Hilbert α}

open Deduction

class HasK (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasK] : Entailment.HasAxiomK H.logic where
  K φ ψ := by
    constructor;
    apply maxm;
    use Axioms.K (.atom (HasK.p H)) (.atom (HasK.q H));
    constructor;
    . exact HasK.mem_K;
    . use (λ b => if (HasK.p H) = b then φ else if (HasK.q H) = b then ψ else (.atom b));
      simp [HasK.ne_pq];
instance [H.HasK] : H.logic.IsNormal where

end Hilbert


protected abbrev Hilbert.K : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K := Hilbert.K.logic
instance : Hilbert.K.HasK where p := 0; q := 1
instance : Entailment.K (Logic.K) where

end LO.Modal
