import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.FiniteFrame

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.TransitiveFrameClass : FrameClass := { F | Transitive F }
abbrev Kripke.TransitiveFiniteFrameClass : FiniteFrameClass := { F | Transitive F.Rel }

instance : TransitiveFrameClass.DefinedBy Hilbert.K4.axioms := by
  convert MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms {⟨0, 2, 1, 0⟩};
  . unfold TransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.transitive_def];
  . exact Hilbert.K4.eq_Geach;

namespace Hilbert.K4

instance Kripke.sound : Sound (Hilbert.K4) (Kripke.TransitiveFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.K4) (TransitiveFrameClass) := ⟨Canonical.transitive⟩

instance Kripke.complete : Complete (Hilbert.K4) (TransitiveFrameClass) := inferInstance

open finestFilterationTransitiveClosureModel in
instance Kripke.finiteComplete : Complete (Hilbert.K4) (TransitiveFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      simp only [FiniteFrameClass.toFrameClass];
      use ⟨FM.toFrame⟩;
      refine ⟨?_, rfl⟩;
      . exact transitive;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val;
  . apply finestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩

end Hilbert.K4

end LO.Modal
