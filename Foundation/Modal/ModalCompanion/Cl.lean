import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Logic.Sublogic.ModalCube
import Foundation.Modal.Kripke.Hilbert.S5


namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke

namespace Logic

lemma gS5_of_Cl (h : φ ∈ Logic.Cl) : φᵍ ∈ Logic.S5 := by
  haveI : Hilbert.S4 ⊢! ◇φᵍ := iff_provable_Cl_provable_dia_gS4.mp h;
  haveI : Hilbert.S4 ⊢! ◇□φᵍ := (diaK'! $ Hilbert.goedelTranslated_axiomTc) ⨀ this;
  exact rm_diabox'! $ Logic.S4_ssubset_S5.1 this;

end Logic


end LO.Modal
