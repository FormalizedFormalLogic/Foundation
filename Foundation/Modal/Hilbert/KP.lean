import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.KD
import Foundation.Modal.Entailment.KP

namespace LO.Modal

variable {H : Hilbert α}

namespace Hilbert

open Deduction

class HasP (H : Hilbert α) where
  mem_P : Axioms.P ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasP] : Entailment.HasAxiomP H.logic where
  P := by
    constructor;
    apply maxm;
    use Axioms.P;
    constructor;
    . exact HasP.mem_P;
    . use (.id);
      simp;

end Hilbert

protected abbrev Hilbert.KP : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.P}⟩
protected abbrev Logic.KP : Logic ℕ := Hilbert.KP.logic
instance : Hilbert.KP.HasK where p := 0; q := 1
instance : Hilbert.KP.HasP where
instance : Entailment.KP (Logic.KP) where

instance : (Logic.KP) ≊ (Logic.KD) := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;
  . apply Hilbert.weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;

end LO.Modal
