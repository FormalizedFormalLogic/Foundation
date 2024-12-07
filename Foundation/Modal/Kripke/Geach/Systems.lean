import Foundation.Modal.Kripke.Geach.Basic

namespace LO.Modal

namespace Hilbert

open Modal.Kripke
open Kripke
open Hilbert.Kripke

namespace KD

instance Kripke.sound : Sound (Hilbert.KD ℕ) (SerialFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SerialFrameClass.is_geach]; apply GeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach, Axioms.MultiGeach.def_one])

instance consistent : System.Consistent (Hilbert.KD ℕ) := instConsistent_of_nonempty_frameclass (C := SerialFrameClass) $ by
  rw [SerialFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

end KD


namespace KT

instance Kripke.sound : Sound (Hilbert.KT ℕ) (ReflexiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveFrameClass.is_geach]; apply GeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach, Axioms.MultiGeach.def_one])

instance consistent : System.Consistent (Hilbert.KT ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveFrameClass) $ by
  rw [ReflexiveFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KT ℕ) ReflexiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KT


namespace KTB

instance Kripke.sound : Sound (Hilbert.KTB ℕ) (ReflexiveSymmetricFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveSymmetricFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KTB ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveSymmetricFrameClass) $ by
  rw [ReflexiveSymmetricFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KTB ℕ) ReflexiveSymmetricFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveSymmetricFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KTB


namespace K4

instance Kripke.sound : Sound (Hilbert.K4 ℕ) (TransitiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [TransitiveFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.K4 ℕ) := instConsistent_of_nonempty_frameclass (C := TransitiveFrameClass) $ by
  rw [TransitiveFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.K4 ℕ) TransitiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [TransitiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end K4


namespace K5

instance Kripke.sound : Sound (Hilbert.K5 ℕ) (EuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [EuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.K5 ℕ) := instConsistent_of_nonempty_frameclass (C := EuclideanFrameClass) $ by
  rw [EuclideanFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.K5 ℕ) EuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [EuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end K5


namespace S4

instance Kripke.sound : Sound (Hilbert.S4 ℕ) (ReflexiveTransitiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveTransitiveFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.S4 ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveTransitiveFrameClass) $ by
  rw [ReflexiveTransitiveFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.S4 ℕ) ReflexiveTransitiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveTransitiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end S4



namespace S5

instance Kripke.sound : Sound (Hilbert.S5 ℕ) (ReflexiveEuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveEuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.S5 ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveEuclideanFrameClass) $ by
  rw [ReflexiveEuclideanFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.S5 ℕ) ReflexiveEuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveEuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end S5


namespace KT4B

instance Kripke.sound : Sound (Hilbert.KT4B ℕ) (ReflexiveTransitiveSymmetricFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveTransitiveSymmetricFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KT4B ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveTransitiveSymmetricFrameClass) $ by
  rw [ReflexiveTransitiveSymmetricFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KT4B ℕ) ReflexiveTransitiveSymmetricFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveTransitiveSymmetricFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KT4B


namespace KD45

instance Kripke.sound : Sound (Hilbert.KD45 ℕ) (SerialTransitiveEuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SerialTransitiveEuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KD45 ℕ) := instConsistent_of_nonempty_frameclass (C := SerialTransitiveEuclideanFrameClass) $ by
  rw [SerialTransitiveEuclideanFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KD45 ℕ) SerialTransitiveEuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [SerialTransitiveEuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KD45


namespace K45

instance Kripke.sound : Sound (Hilbert.K45 ℕ) (TransitiveEuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [TransitiveEuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.K45 ℕ) := instConsistent_of_nonempty_frameclass (C := TransitiveEuclideanFrameClass) $ by
  rw [TransitiveEuclideanFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.K45 ℕ) TransitiveEuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [TransitiveEuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end K45


namespace KB4

instance Kripke.sound : Sound (Hilbert.KB4 ℕ) (SymmetricTransitiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SymmetricTransitiveFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KB4 ℕ) := instConsistent_of_nonempty_frameclass (C := SymmetricTransitiveFrameClass) $ by
  rw [SymmetricTransitiveFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KB4 ℕ) SymmetricTransitiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [SymmetricTransitiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KB4


namespace KB5

instance Kripke.sound : Sound (Hilbert.KB5 ℕ) (SymmetricEuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SymmetricEuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KB5 ℕ) := instConsistent_of_nonempty_frameclass (C := SymmetricEuclideanFrameClass) $ by
  rw [SymmetricEuclideanFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KB5 ℕ) SymmetricEuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [SymmetricEuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KB5


namespace KDB

instance Kripke.sound : Sound (Hilbert.KDB ℕ) (SerialSymmetricFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SerialSymmetricFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance consistent : System.Consistent (Hilbert.KDB ℕ) := instConsistent_of_nonempty_frameclass (C := SerialSymmetricFrameClass) $ by
  rw [SerialSymmetricFrameClass.is_geach];
  exact MultiGeachConfluentFrameClass.nonempty;

instance Kripke.complete : Complete (Hilbert.KDB ℕ) SerialSymmetricFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [SerialSymmetricFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

end KDB


end Hilbert

end LO.Modal
