import Foundation.Modal.Logic.Basic
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

namespace Logic

protected abbrev K4 : Logic := Hilbert.K4.logic

protected abbrev S4 : Logic := Hilbert.S4.logic
instance : (Logic.S4).Normal := Hilbert.normal

protected abbrev S5 : Logic := Hilbert.S5.logic
instance : (Logic.S5).Normal := Hilbert.normal

protected abbrev GL : Logic := Hilbert.GL.logic
instance : (Logic.GL).Normal := Hilbert.normal

protected abbrev Grz : Logic := Hilbert.Grz.logic
instance : (Logic.Grz).Normal := Hilbert.normal

end Logic

end LO.Modal
