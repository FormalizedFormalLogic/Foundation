import Foundation.Modal.Hilbert.Maximal.Unprovability
import Foundation.Modal.Kripke.Hilbert.GL.MDP
import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.Hilbert.K45
import Foundation.Modal.Kripke.Hilbert.K4Point2
import Foundation.Modal.Kripke.Hilbert.K4Point3
import Foundation.Modal.Kripke.Hilbert.K5
import Foundation.Modal.Kripke.Hilbert.KB
import Foundation.Modal.Kripke.Hilbert.KB4
import Foundation.Modal.Kripke.Hilbert.KB5
import Foundation.Modal.Kripke.Hilbert.KD
import Foundation.Modal.Kripke.Hilbert.KD4
import Foundation.Modal.Kripke.Hilbert.KD45
import Foundation.Modal.Kripke.Hilbert.KD5
import Foundation.Modal.Kripke.Hilbert.KDB
import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KTB
import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.Hilbert.S4Point2
import Foundation.Modal.Kripke.Hilbert.S4Point3
import Foundation.Modal.Kripke.Hilbert.GrzPoint2
import Foundation.Modal.Kripke.Hilbert.GrzPoint3
import Foundation.Modal.Kripke.Hilbert.GLPoint3
import Foundation.Modal.Kripke.Hilbert.S5
import Foundation.Modal.Kripke.Hilbert.Triv
import Foundation.Modal.Kripke.Hilbert.Ver
import Foundation.Modal.Kripke.Hilbert.KTc
import Foundation.Modal.Hilbert.S5Grz
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Entailment.KT
import Foundation.Modal.Kripke.KH_Incompleteness

namespace LO.Modal

namespace Logic

protected abbrev Empty : Logic := ∅

protected abbrev Univ : Logic := Set.univ

protected abbrev K4 : Logic := Hilbert.K4.logic
lemma K4.eq_TransitiveKripkeFrameClass_Logic : Logic.K4 = Kripke.FrameClass.trans.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K4Point2 : Logic := Hilbert.K4Point2.logic
lemma K4Point2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic : Logic.K4Point2 = Kripke.FrameClass.trans_weakConfluent.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K4Point3 : Logic := Hilbert.K4Point3.logic
lemma K4Point3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic : Logic.K4Point3 = Kripke.FrameClass.trans_weakConnected.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K45 : Logic := Hilbert.K45.logic
lemma K45.eq_TransitiveEuclideanKripkeFrameClass_Logic : Logic.K45 = Kripke.FrameClass.trans_eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K5 : Logic := Hilbert.K5.logic
lemma K5.eq_EuclideanKripkeFrameClass_Logic : Logic.K5 = Kripke.FrameClass.eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB : Logic := Hilbert.KB.logic
lemma KB.eq_SymmetricKripkeFrameClass_Logic : Logic.KB = Kripke.FrameClass.symm.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB4 : Logic := Hilbert.KB4.logic
lemma KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic : Logic.KB4 = Kripke.FrameClass.symm_trans.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB5 : Logic := Hilbert.KB5.logic
lemma KB5.eq_ReflexiveEuclideanKripkeFrameClass_Logic : Logic.KB5 = Kripke.FrameClass.symm_eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD : Logic := Hilbert.KD.logic
lemma KD.eq_SerialKripkeFrameClass_Logic : Logic.KD = Kripke.FrameClass.serial.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD4 : Logic := Hilbert.KD4.logic
lemma KD4.eq_SerialTransitiveKripkeFrameClass_Logic : Logic.KD4 = Kripke.FrameClass.serial_trans.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD45 : Logic := Hilbert.KD45.logic
lemma KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic : Logic.KD45 = Kripke.FrameClass.serial_trans_eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD5 : Logic := Hilbert.KD5.logic
lemma KD5.eq_SerialEuclideanKripkeFrameClass_Logic : Logic.KD5 = Kripke.FrameClass.serial_eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KDB : Logic := Hilbert.KDB.logic
lemma KDB.eq_SerialSymmetricKripkeFrameClass_Logic : Logic.KDB = Kripke.FrameClass.serial_symm.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KT : Logic := Hilbert.KT.logic
lemma KT.eq_ReflexiveKripkeFrameClass_Logic : Logic.KT = Kripke.FrameClass.refl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KTB : Logic := Hilbert.KTB.logic
lemma KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic : Logic.KTB = Kripke.FrameClass.refl_symm.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4 : Logic := Hilbert.S4.logic
lemma S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic : Logic.S4 = Kripke.FrameClass.preorder.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4Point2 : Logic := Hilbert.S4Point2.logic
lemma S4Point2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic : Logic.S4Point2 = Kripke.FrameClass.confluent_preorder.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4Point3 : Logic := Hilbert.S4Point3.logic
lemma S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic : Logic.S4Point3 = Kripke.FrameClass.connected_preorder.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S5 : Logic := Hilbert.S5.logic
lemma S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic : Logic.S5 = Kripke.FrameClass.refl_eucl.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma S5.eq_UniversalKripkeFrameClass_Logic : Logic.S5 = Kripke.FrameClass.universal.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev S5Grz : Logic := Hilbert.S5Grz.logic

protected abbrev GL : Logic := Hilbert.GL.logic
lemma GL.eq_TransitiveIrreflexiveFiniteKripkeFrameClass_Logic : Logic.GL = Kripke.FrameClass.finite_trans_irrefl.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
instance : (Logic.GL).Unnecessitation := inferInstance

protected abbrev GLPoint3 : Logic := Hilbert.GLPoint3.logic
lemma GLPoint3.Kripke.eq_finiteStrictLinearOrder_logic : Logic.GLPoint3 = Kripke.FrameClass.finite_strict_linear_order.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev KH : Logic := Hilbert.KH.logic

protected abbrev Grz : Logic := Hilbert.Grz.logic
lemma Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic : Logic.Grz = Kripke.FrameClass.finite_partial_order.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev GrzPoint2 : Logic := Hilbert.GrzPoint2.logic
lemma GrzPoint2.eq_ReflexiveTransitiveAntiSymmetricConfluentFiniteKripkeFrameClass_Logic : Logic.GrzPoint2 = Kripke.FrameClass.finite_confluent_partial_order.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev GrzPoint3 : Logic := Hilbert.GrzPoint3.logic
lemma GrzPoint3.eq_ReflexiveTransitiveAntiSymmetricConnectedFiniteKripkeFrameClass_Logic : Logic.GrzPoint3 = Kripke.FrameClass.finite_connected_partial_order.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev Triv : Logic := Hilbert.Triv.logic
lemma Triv.eq_EqualityKripkeFrameClass_Logic : Logic.Triv = Kripke.FrameClass.equality.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Triv.Kripke.eq_finite_equality_logic : Logic.Triv = Kripke.FrameClass.finite_equality.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev Ver : Logic := Hilbert.Ver.logic
instance : (Logic.Ver).Normal := Hilbert.normal
lemma Ver.eq_IsolatedFrameClass_Logic : Logic.Ver = Kripke.FrameClass.isolated.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KTc : Logic := Hilbert.KTc.logic
lemma KTc.eq_CoreflexiveKripkeFrameClass_Logic : Logic.KTc = Kripke.FrameClass.corefl.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic

end LO.Modal
