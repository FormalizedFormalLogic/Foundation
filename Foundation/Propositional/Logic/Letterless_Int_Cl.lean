import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Modal.Maximal.Makinson
import Foundation.Modal.ModalCompanion.Int
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO.Propositional

@[simp]
def Formula.goedelTranslate.letterless {φ : Formula ℕ} (hφ : φ.letterless) : φᵍ.letterless := by
  induction φ <;> simp_all [Formula.letterless, Modal.Formula.letterless]


namespace Logic

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

theorem iff_letterless_Int_Cl {φ : Formula ℕ} (hφ : φ.letterless) : 𝗜𝐧𝐭 ⊢! φ ↔ 𝐂𝐥 ⊢! φ := by
  constructor;
  . apply WeakerThan.wk;
    infer_instance;
  . intro h;
    have : Modal.Hilbert.S4 ⊢! ◇φᵍ := Modal.Logic.iff_provable_Cl_provable_dia_gS4.mp h;
    have : Modal.Hilbert.Triv ⊢! ◇φᵍ := WeakerThan.pbl this;
    have : Modal.Hilbert.Triv ⊢! φᵍ := diaT'! this;
    have : (φᵍᵀ.toPropFormula _).isTautology := Modal.Logic.Triv.iff_isTautology.mp this;
    have : Modal.KD ⊢! φᵍ := Modal.Logic.provable_KD_of_classical_tautology (Formula.goedelTranslate.letterless hφ) this;
    have : Modal.S4 ⊢! φᵍ := WeakerThan.pbl this;
    exact Modal.modalCompanion_Int_S4.companion.mpr this;

end Logic

end LO.Propositional
