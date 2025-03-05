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
lemma K4.eq_TransitiveKripkeFrameClass_Logic : Logic.K4 = Kripke.TransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K4Point2 : Logic := Hilbert.K4Point2.logic
lemma K4Point2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic : Logic.K4Point2 = Kripke.TransitiveWeakConfluentFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K4Point3 : Logic := Hilbert.K4Point3.logic
lemma K4Point3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic : Logic.K4Point3 = Kripke.TransitiveWeakConnectedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K45 : Logic := Hilbert.K45.logic
lemma K45.eq_TransitiveEuclideanKripkeFrameClass_Logic : Logic.K45 = Kripke.TransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev K5 : Logic := Hilbert.K5.logic
lemma K5.eq_EuclideanKripkeFrameClass_Logic : Logic.K5 = Kripke.EuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB : Logic := Hilbert.KB.logic
lemma KB.eq_SymmetricKripkeFrameClass_Logic : Logic.KB = Kripke.SymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB4 : Logic := Hilbert.KB4.logic
lemma KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic : Logic.KB4 = Kripke.SymmetricTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KB5 : Logic := Hilbert.KB5.logic
lemma KB5.eq_ReflexiveEuclideanKripkeFrameClass_Logic : Logic.KB5 = Kripke.SymmetricEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD : Logic := Hilbert.KD.logic
lemma KD.eq_SerialKripkeFrameClass_Logic : Logic.KD = Kripke.SerialFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD4 : Logic := Hilbert.KD4.logic
lemma KD4.eq_SerialTransitiveKripkeFrameClass_Logic : Logic.KD4 = Kripke.SerialTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD45 : Logic := Hilbert.KD45.logic
lemma KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic : Logic.KD45 = Kripke.SerialTransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD5 : Logic := Hilbert.KD5.logic
lemma KD5.eq_SerialEuclideanKripkeFrameClass_Logic : Logic.KD5 = Kripke.SerialEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KDB : Logic := Hilbert.KDB.logic
lemma KDB.eq_SerialSymmetricKripkeFrameClass_Logic : Logic.KDB = Kripke.SerialSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KT : Logic := Hilbert.KT.logic
lemma KT.eq_ReflexiveKripkeFrameClass_Logic : Logic.KT = Kripke.ReflexiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KTB : Logic := Hilbert.KTB.logic
lemma KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic : Logic.KTB = Kripke.ReflexiveSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4 : Logic := Hilbert.S4.logic
lemma S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic : Logic.S4 = Kripke.ReflexiveTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4Point2 : Logic := Hilbert.S4Point2.logic
lemma S4Point2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic : Logic.S4Point2 = Kripke.ReflexiveTransitiveConfluentFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4Point3 : Logic := Hilbert.S4Point3.logic
lemma S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic : Logic.S4Point3 = Kripke.ReflexiveTransitiveConnectedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev S5 : Logic := Hilbert.S5.logic
lemma S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic : Logic.S5 = Kripke.ReflexiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma S5.eq_UniversalKripkeFrameClass_Logic : Logic.S5 = Kripke.UniversalFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

protected abbrev S5Grz : Logic := Hilbert.S5Grz.logic


protected abbrev GL : Logic := Hilbert.GL.logic
lemma GL.eq_TransitiveIrreflexiveFiniteKripkeFrameClass_Logic : Logic.GL = Kripke.TransitiveIrreflexiveFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
instance : (Logic.GL).Unnecessitation := inferInstance


protected abbrev KH : Logic := Hilbert.KH.logic


protected abbrev Grz : Logic := Hilbert.Grz.logic
lemma Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic : Logic.Grz = Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic


protected abbrev Triv : Logic := Hilbert.Triv.logic
lemma Triv.eq_EqualityKripkeFrameClass_Logic : Logic.Triv = Kripke.EqualityFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev Ver : Logic := Hilbert.Ver.logic
instance : (Logic.Ver).Normal := Hilbert.normal
lemma Ver.eq_IsolatedFrameClass_Logic : Logic.Ver = Kripke.IsolatedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KTc : Logic := Hilbert.KTc.logic
lemma KTc.eq_CoreflexiveKripkeFrameClass_Logic : Logic.KTc = Kripke.CoreflexiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic

end LO.Modal
