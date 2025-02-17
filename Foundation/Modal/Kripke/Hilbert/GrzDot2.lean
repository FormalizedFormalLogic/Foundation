import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Dot2

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

abbrev ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel ∧ Confluent F.Rel }

instance : ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Dot2 (atom 0)} := by
  have h₁ := restrictFin_definability {Axioms.Dot2 (atom 0)} ({F | Confluent F}) $ by
    convert MultiGeacheanFrameClass.isDefinedByGeachAxioms ({⟨1, 1, 1, 1⟩});
    . ext;
      simp only [MultiGeachean, Set.mem_singleton_iff, forall_eq];
      apply Geachean.confluent_def;
    . simp;
  have := @FiniteFrameClass.definedBy_inter
    ReflexiveTransitiveAntiSymmetricFiniteFrameClass
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)})
    inferInstance
    { F | Confluent F.Rel}
    {Axioms.Dot2 (atom 0)}
    h₁;
  have e₁ :
    (ReflexiveTransitiveAntiSymmetricFiniteFrameClass ∩ {F | Confluent F.Rel}) =
    (ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass) := by
      ext F;
      simp;
      tauto;
  have e₂ :
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)} ∪ {Axioms.Dot2 (atom 0)}) =
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Dot2 (atom 0)} : Set (Formula ℕ)) := by
      ext φ;
      constructor;
      . rintro (⟨_, _⟩ | _) <;> tauto;
      . rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp_all;
  rwa [e₁, e₂] at this;

instance : ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, AntiSymmetric, Confluent];

end Kripke


namespace Hilbert.GrzDot2

instance Kripke.sound : Sound (Hilbert.GrzDot2) (Kripke.ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.GrzDot2) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass

end Hilbert.GrzDot2

end LO.Modal
