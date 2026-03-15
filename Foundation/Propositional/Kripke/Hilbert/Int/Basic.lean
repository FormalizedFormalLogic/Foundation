module

public import Foundation.Propositional.Kripke.Completeness
public import Foundation.Propositional.Kripke.Hilbert.Basic
public import Foundation.Propositional.Kripke.Filtration

@[expose] public section

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Hilbert.Int

instance : (Set.univ : FrameClass) ⊧* (Hilbert.Int : Hilbert ℕ) := by
  constructor;
  rintro φ ⟨_, rfl⟩ F;
  grind;

instance soundKripke : Sound Hilbert.Int (Set.univ : FrameClass) := inferInstance

instance : Entailment.Consistent (Hilbert.Int : Hilbert ℕ) := consistent_of_nonempty_frameClass Set.univ (by simp)

instance : Canonical (Hilbert.Int : Hilbert ℕ) (Set.univ : FrameClass) := by tauto;

instance completeKripke : Complete (Hilbert.Int : Hilbert ℕ) (Set.univ : FrameClass) := inferInstance

instance : Complete (Hilbert.Int : Hilbert ℕ) ({ F : Frame | Finite F }) := by
  constructor;
  intro φ hφ;
  apply Complete.complete (𝓜 := (Set.univ : FrameClass));
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFiltrationModel M ↑φ.subformulas;
  apply filtration FM (coarsestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  apply FilterEqvQuotient.finite;
  simp;

end Hilbert.Int

end LO.Propositional

end
