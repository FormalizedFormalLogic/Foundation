import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Cl
import Foundation.Propositional.Kripke.Hilbert.KC
import Foundation.Propositional.Kripke.Hilbert.LC
import Foundation.Propositional.Kripke.Hilbert.KP

namespace LO.Propositional

namespace Logic

protected abbrev KC : Logic := Hilbert.KC.logic
lemma KC.Kripke.eq_confluent : Logic.KC = Kripke.FrameClass.confluent.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma KC.Kripke.eq_finite_confluent : Logic.KC = Kripke.FrameClass.finite_confluent.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev LC : Logic := Hilbert.LC.logic
lemma LC.Kripke.eq_connected : Logic.LC = Kripke.FrameClass.connected.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma LC.Kripke.eq_finite_connected : Logic.LC = Kripke.FrameClass.finite_connected.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev Cl : Logic := Hilbert.Cl.logic
lemma Cl.Kripke.eq_euclidean : Logic.Cl = Kripke.FrameClass.euclidean.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Cl.Kripke.eq_finite_euclidean : Logic.Cl = Kripke.FrameClass.finite_euclidean.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Cl.Kripke.eq_finite_symmetric : Logic.Cl = Kripke.FrameClass.finite_symmetric.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KP : Logic := Hilbert.KP.logic
lemma KP.Kripke.eq_krieselputnam : Logic.KP = Kripke.FrameClass.krieselputnam.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic

end LO.Propositional
