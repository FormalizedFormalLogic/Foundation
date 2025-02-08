import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.System.KD
import Foundation.Modal.System.KP

namespace LO.Modal.Hilbert

variable {H : Hilbert α}

open Deduction

section

class HasP (H : Hilbert α) where
  mem_P : Axioms.P ∈ H.axioms := by tauto;

instance [DecidableEq α] [hP : H.HasP] : System.HasAxiomP H where
  P := by
    apply maxm;
    use Axioms.P;
    constructor;
    . exact hP.mem_P;
    . use (.id); simp;

end

protected abbrev KP : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.P}⟩
instance : Hilbert.KP.HasK where p := 0; q := 1
instance : Hilbert.KP.HasP where
instance : System.KP (Hilbert.KP) where

open System in
theorem iff_provable_KP_provable_KD : (Hilbert.KP ⊢! φ) ↔ (Hilbert.KD ⊢! φ) := by
  constructor;
  . apply weakerThan_of_dominate_axioms;
    rintro φ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomP!];
  . apply weakerThan_of_dominate_axioms;
    rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩)) <;> simp only [axiomK!, axiomD!];

end LO.Modal.Hilbert
