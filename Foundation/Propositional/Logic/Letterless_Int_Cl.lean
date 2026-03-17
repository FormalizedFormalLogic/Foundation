module

public import Foundation.Modal.ModalCompanion.Standard.Int
public import Foundation.Modal.ModalCompanion.Standard.Cl
public import Foundation.Modal.Maximal.Makinson

@[expose] public section

namespace LO.Propositional

@[simp, grind .]
lemma Formula.gödelTranslate.Letterless {φ : Formula ℕ} (hφ : φ.Letterless) : φᵍ.Letterless := by
  induction φ <;> . simp_all only [Formula.gödelTranslate]; grind;

open LO.Entailment LO.Modal.Entailment

theorem iff_letterless_Int_Cl {φ : Formula ℕ} (hφ : φ.Letterless) : φ ∈ Propositional.Int ↔ φ ∈ Propositional.Cl := by
  constructor;
  . apply WeakerThan.wk;
    infer_instance;
  . intro h;
    apply Propositional.Int.modalCompanion_S4.mpr
      $ WeakerThan.pbl
      $ Modal.Logic.provable_KD_of_classical_tautology (by grind)
      $ Modal.Triv.iff_tautology.mp
      $ diaT'!
      $ WeakerThan.pbl
      $ Cl.iff_mem_S4_dia.mp h;

end LO.Propositional

end
