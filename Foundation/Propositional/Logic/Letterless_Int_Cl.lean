import Foundation.Modal.Maximal.Makinson
import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Propositional.Logic.Sublogic

namespace LO.Propositional

@[simp]
def Formula.goedelTranslate.letterless {φ : Formula ℕ} (hφ : φ.letterless) : φᵍ.letterless := by
  induction φ <;> simp_all [Formula.letterless, goedelTranslate, Modal.Formula.letterless]


namespace Logic

open Entailment

theorem iff_letterless_Int_Cl {φ : Formula ℕ} (hφ : φ.letterless) : φ ∈ Logic.Int ↔ φ ∈ Logic.Cl := by
  constructor;
  . apply Int_ssubset_Cl.1;
  . intro h;
    have : ◇φᵍ ∈ Modal.Logic.S4 := Modal.Logic.iff_provable_Cl_provable_dia_gS4.mp h;
    have : ◇φᵍ ∈ Modal.Logic.Triv := Modal.Logic.Sublogic.subset (L₁ := Modal.Logic.S4) (L₂ := Modal.Logic.Triv) this;
    have : φᵍ ∈ Modal.Logic.Triv := diaT'! this;
    have : Hilbert.Cl ⊢! φᵍᵀ.toPropFormula _ := Modal.Hilbert.Triv.iff_provable_Cl.mp this;
    have : Semantics.Valid (ClassicalSemantics.Valuation ℕ) (φᵍᵀ.toPropFormula _) := Hilbert.Cl.soundness this;
    have : φᵍ ∈ Modal.Logic.KD := Modal.Logic.provable_KD_of_classical_tautology (Formula.goedelTranslate.letterless hφ) this;
    have : φᵍ ∈ Modal.Logic.S4 := Modal.Logic.Sublogic.subset (L₁ := Modal.Logic.KD) (L₂ := Modal.Logic.S4) this;
    exact Modal.modalCompanion_Int_S4.companion.mpr this;

end Logic

end LO.Propositional
