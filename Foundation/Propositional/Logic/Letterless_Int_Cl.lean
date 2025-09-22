import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Modal.Maximal.Makinson
import Foundation.Modal.ModalCompanion.Int
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO.Propositional

@[simp, grind]
lemma Formula.goedelTranslate.Letterless {φ : Formula ℕ} (hφ : φ.Letterless) : φᵍ.Letterless := by
  induction φ with
  | himp | hand | hor => simp_all only [Formula.goedelTranslate]; grind;
  | _ => simp_all [Formula.goedelTranslate];


namespace Logic

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

theorem iff_letterless_Int_Cl {φ : Formula ℕ} (hφ : φ.Letterless) : 𝐈𝐧𝐭 ⊢! φ ↔ 𝐂𝐥 ⊢! φ := by
  constructor;
  . apply WeakerThan.wk;
    infer_instance;
  . intro h;
    have : Modal.S4 ⊢! ◇φᵍ := Modal.iff_provable_Cl_provable_dia_gS4.mp h;
    have : Modal.Triv ⊢! ◇φᵍ := WeakerThan.pbl this;
    have : Modal.Triv ⊢! φᵍ := diaT'! this;
    have : (φᵍᵀ.toPropFormula _).isTautology := Modal.Triv.iff_isTautology.mp this;
    have : Modal.KD ⊢! φᵍ := Modal.Logic.provable_KD_of_classical_tautology (by grind) this;
    have : Modal.S4 ⊢! φᵍ := WeakerThan.pbl this;
    exact Modal.ModalCompanion.companion.mpr this;

end Logic

end LO.Propositional
