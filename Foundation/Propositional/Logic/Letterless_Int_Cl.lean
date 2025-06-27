import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Modal.Maximal.Makinson
import Foundation.Modal.ModalCompanion.Int
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO.Propositional

@[simp]
def Formula.goedelTranslate.letterless {φ : Formula ℕ} (hφ : φ.letterless) : φᵍ.letterless := by
  induction φ <;> simp_all [Formula.letterless, goedelTranslate, Modal.Formula.letterless]


namespace Logic

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

theorem iff_letterless_Int_Cl {φ : Formula ℕ} (hφ : φ.letterless) : φ ∈ Logic.Int ↔ φ ∈ Logic.Cl := by
  constructor;
  . apply Propositional.Logic.Cl.proper_extension_of_Int.1;
  . intro h;
    have : Modal.Logic.S4 ⊢! ◇φᵍ := Modal.Logic.iff_provable_Cl_provable_dia_gS4.mp h;
    have : Modal.Logic.Triv ⊢! ◇φᵍ := WeakerThan.pbl this;
    have : Modal.Logic.Triv ⊢! φᵍ := diaT'! this;
    have : Hilbert.Cl ⊢! φᵍᵀ.toPropFormula _ := Modal.Logic.Triv.iff_provable_Cl.mp this;
    have : Semantics.Valid (ClassicalSemantics.Valuation ℕ) (φᵍᵀ.toPropFormula _) := Hilbert.Cl.soundness this;
    have : Modal.Logic.KD ⊢! φᵍ := Modal.Logic.provable_KD_of_classical_tautology (Formula.goedelTranslate.letterless hφ) this;
    have : Modal.Logic.S4 ⊢! φᵍ := WeakerThan.pbl this;
    exact Modal.modalCompanion_Int_S4.companion.mpr this;

end Logic

end LO.Propositional
