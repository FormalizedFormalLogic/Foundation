import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke2.Completeness
import Foundation.Modal.Kripke2.Basic
import Foundation.Modal.Hilbert2.Geach

def MultiGeachean (ts : Set GeachConfluent.Taple) (R : Rel α α) := ∀ t ∈ ts, GeachConfluent t R


namespace LO.Modal

namespace Kripke

abbrev GeachConfluentFrameClass (t : GeachConfluent.Taple) : FrameClass := { F | (GeachConfluent t) F.Rel }

instance GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass t).Nonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  intros x _ _ _; use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }


abbrev MultiGeacheanConfluentFrameClass (ts : Set GeachConfluent.Taple) : FrameClass := { F | (MultiGeachean ts) F.Rel }

instance MultiGeacheanConfluentFrameClass.nonempty : (MultiGeacheanConfluentFrameClass ts).Nonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

open Formula.Kripke

instance MultiGeachConfluentFrameClass.isDefinedBy (ts) : (MultiGeacheanConfluentFrameClass ts).DefinedBy (ts.image (λ t => Axioms.Geach t (.atom 0))) := by
  unfold MultiGeacheanConfluentFrameClass MultiGeachean Axioms.Geach;
  constructor;
  intro F;
  constructor;
  . rintro hF φ ⟨t, ⟨ht, rfl⟩⟩ V x h;
    obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨u, Ryu, Rzu⟩ := hF t ht ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (Satisfies.multibox_def.mp hbp) Ryu;
  . rintro h t ht x y z ⟨Rxy, Rxz⟩;
    let V : Kripke.Valuation F := λ v _ => y ≺^[t.m] v;
    have : Satisfies ⟨F, V⟩ x (◇^[t.i](□^[t.m](.atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . assumption;
      . apply Satisfies.multibox_def.mpr;
        aesop;
    have : Satisfies ⟨F, V⟩ x (□^[t.j](◇^[t.n]Formula.atom 0)) := h (Axioms.Geach t (.atom 0)) (by tauto) V x this;
    have : Satisfies ⟨F, V⟩ z (◇^[t.n]Formula.atom 0) := Satisfies.multibox_def.mp this Rxz;
    obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this;
    exact ⟨u, Ryu, Rzu⟩;

instance GeachConfluentFrameClass.isDefinedBy (t) : (GeachConfluentFrameClass t).DefinedByFormula (Axioms.Geach t (.atom 0)) := by
  have := MultiGeachConfluentFrameClass.isDefinedBy {t};
  simp at this;
  constructor;
  intro F;
  constructor;
  . rintro hF _ ⟨_, rfl⟩;
    apply this.defines F |>.mp;
    . simp_all [MultiGeachean];
    . simp;
  . intro h;
    apply this.defines F |>.mpr <;> tauto;


section

abbrev ReflexiveFrameClass   : FrameClass := { F | Reflexive F.Rel }
abbrev SerialFrameClass      : FrameClass := { F | Serial F.Rel }
abbrev SymmetricFrameClass   : FrameClass := { F | Symmetric F.Rel }
abbrev TransitiveFrameClass  : FrameClass := { F | Transitive F.Rel }
abbrev EuclideanFrameClass   : FrameClass := { F | Euclidean F.Rel }
abbrev ConfluentFrameClass   : FrameClass := { F | Confluent F.Rel }
abbrev FunctionalFrameClass  : FrameClass := { F | Functional F.Rel }
abbrev CoreflexiveFrameClass : FrameClass := { F | Coreflexive F.Rel }
abbrev DenseFrameClass       : FrameClass := { F | Dense F.Rel }

abbrev ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }
abbrev ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }
abbrev ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }
abbrev ReflexiveTransitiveConfluentFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F }
abbrev ReflexiveTransitiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
abbrev SerialTransitiveEuclideanFrameClass : FrameClass := { F | Serial F ∧ Transitive F ∧ Euclidean F }
abbrev TransitiveEuclideanFrameClass : FrameClass := { F | Transitive F ∧ Euclidean F }
abbrev SymmetricTransitiveFrameClass : FrameClass := { F | Symmetric F ∧ Transitive F }
abbrev SymmetricEuclideanFrameClass : FrameClass := { F | Symmetric F ∧ Euclidean F }
abbrev SerialSymmetricFrameClass : FrameClass := { F | Serial F ∧ Symmetric F }
abbrev SerialTransitiveFrameClass : FrameClass := { F | Serial F ∧ Transitive F }
abbrev SerialEuclideanFrameClass : FrameClass := { F | Serial F ∧ Euclidean F }

end


instance ReflexiveFrameClass.DefinedByAxiomT : ReflexiveFrameClass.DefinedByFormula (Axioms.T (.atom 0)) := by
  rw [
    (show ReflexiveFrameClass = GeachConfluentFrameClass ⟨0, 0, 1, 0⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.reflexive_def
    ),
    (show Axioms.T (.atom 0) = (Axioms.Geach ⟨0, 0, 1, 0⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance SerialFrameClass.DefinedByAxiomD : SerialFrameClass.DefinedByFormula (Axioms.D (.atom 0)) := by
  rw [
    (show SerialFrameClass = GeachConfluentFrameClass ⟨0, 0, 1, 1⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.serial_def;
    ),
    (show Axioms.D (.atom 0) = (Axioms.Geach ⟨0, 0, 1, 1⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance SymmetricFrameClass.DefinedByAxiomB : SymmetricFrameClass.DefinedByFormula (Axioms.B (.atom 0)) := by
  rw [
    (show SymmetricFrameClass = GeachConfluentFrameClass ⟨0, 1, 0, 1⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.symmetric_def;
    ),
    (show Axioms.B (.atom 0) = (Axioms.Geach ⟨0, 1, 0, 1⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance TransitiveFrameClass.DefinedByAxiomFour : TransitiveFrameClass.DefinedByFormula (Axioms.Four (.atom 0)) := by
  rw [
    (show TransitiveFrameClass = GeachConfluentFrameClass ⟨0, 2, 1, 0⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.transitive_def;
    ),
    (show Axioms.Four (.atom 0) = (Axioms.Geach ⟨0, 2, 1, 0⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance EuclideanFrameClass.DefinedByAxiomFive : EuclideanFrameClass.DefinedByFormula (Axioms.Five (.atom 0)) := by
  rw [
    (show EuclideanFrameClass = GeachConfluentFrameClass ⟨1, 1, 0, 1⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.euclidean_def;
    ),
    (show Axioms.Five (.atom 0) = (Axioms.Geach ⟨1, 1, 0, 1⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance ConfluentFrameClass.DefinedByAxiomDot2 : ConfluentFrameClass.DefinedByFormula (Axioms.Dot2 (.atom 0)) := by
  rw [
    (show ConfluentFrameClass = GeachConfluentFrameClass ⟨1, 1, 1, 1⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.confluent_def;
    ),
    (show Axioms.Dot2 (.atom 0) = (Axioms.Geach ⟨1, 1, 1, 1⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance FunctionalFrameClass.DefinedByAxiomCD : FunctionalFrameClass.DefinedByFormula (Axioms.CD (.atom 0)) := by
  rw [
    (show FunctionalFrameClass = GeachConfluentFrameClass ⟨1, 1, 0, 0⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.functional_def;
    ),
    (show Axioms.CD (.atom 0) = (Axioms.Geach ⟨1, 1, 0, 0⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance CoreflexiveFrameClass.DefinedByAxiomTc : CoreflexiveFrameClass.DefinedByFormula (Axioms.Tc (.atom 0)) := by
  rw [
    (show CoreflexiveFrameClass = GeachConfluentFrameClass ⟨0, 1, 0, 0⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.extensive_def;
    ),
    (show Axioms.Tc (.atom 0) = (Axioms.Geach ⟨0, 1, 0, 0⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;


instance DenseFrameClass.DefinedByAxiomC4 : DenseFrameClass.DefinedByFormula (Axioms.C4 (.atom 0)) := by
  rw [
    (show DenseFrameClass = GeachConfluentFrameClass ⟨0, 1, 2, 0⟩ by
      ext;
      simp only [Set.mem_setOf_eq];
      exact GeachConfluent.dense_def;
    ),
    (show Axioms.C4 (.atom 0) = (Axioms.Geach ⟨0, 1, 2, 0⟩ (Formula.atom 0)) by rfl)
  ];
  exact GeachConfluentFrameClass.isDefinedBy _;

end Kripke

end LO.Modal
