import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Cl
import Foundation.Propositional.Kripke.Hilbert.KC
import Foundation.Propositional.Kripke.Hilbert.LC

namespace LO.Propositional

namespace Logic

protected abbrev KC : Logic := Hilbert.KC.logic
lemma KC.eq_ConfluentKripkeFrameClass_Logic : Logic.KC = Kripke.ConfluentFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev LC : Logic := Hilbert.LC.logic
lemma LC.eq_ConnectedKripkeFrameClass_Logic : Logic.LC = Kripke.ConnectedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev Cl : Logic := Hilbert.Cl.logic

end Logic

end LO.Propositional
