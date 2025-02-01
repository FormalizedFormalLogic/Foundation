import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke2.Completeness
import Foundation.Modal.Kripke2.Definability
import Foundation.Modal.Hilbert2.Geach

def MultiGeachean (ts : Set GeachConfluent.Taple) (R : Rel α α) := ∀ t ∈ ts, GeachConfluent t R


namespace LO.Modal

namespace Kripke

abbrev GeachConfluentFrameClass (t : GeachConfluent.Taple) : FrameClass := { F | (GeachConfluent t) F.Rel }

instance GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass t).Nonempty := by
  use reflexivePointFrame.toFrame;
  intros x _ _ _; use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }


abbrev MultiGeacheanConfluentFrameClass (ts : Set GeachConfluent.Taple) : FrameClass := { F | (MultiGeachean ts) F.Rel }

instance MultiGeacheanConfluentFrameClass.nonempty : (MultiGeacheanConfluentFrameClass ts).Nonempty := by
  use reflexivePointFrame.toFrame;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }



section

abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F.Rel }
abbrev SerialFrameClass : FrameClass := { F | Serial F.Rel }
abbrev SymmetricFrameClass : FrameClass := { F | Symmetric F.Rel }
abbrev TransitiveFrameClass : FrameClass := { F | Transitive F.Rel }
abbrev EuclideanFrameClass : FrameClass := { F | Euclidean F.Rel }
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

instance ReflexiveFrameClass.isDefinedBy : ReflexiveFrameClass.DefinedBy {(Axioms.T (.atom 0))} := by
  simpa [Axioms.Geach, MultiGeacheanConfluentFrameClass, MultiGeachean, GeachConfluent]
  using MultiGeachConfluentFrameClass.isDefinedBy {⟨0, 0, 1, 0⟩}

end Kripke

end LO.Modal
