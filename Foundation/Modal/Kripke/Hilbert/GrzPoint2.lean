import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Point2

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

abbrev ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel ∧ Confluent F.Rel }

instance : ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Point2 (atom 0)} := by
  have h₁ := restrictFin_definability {Axioms.Point2 (atom 0)} ({F | Confluent F}) $ by
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
    {Axioms.Point2 (atom 0)}
    h₁;
  have e₁ :
    (ReflexiveTransitiveAntiSymmetricFiniteFrameClass ∩ {F | Confluent F.Rel}) =
    (ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass) := by
      ext F;
      simp;
      tauto;
  have e₂ :
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)} ∪ {Axioms.Point2 (atom 0)}) =
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Point2 (atom 0)} : Set (Formula ℕ)) := by
      ext φ;
      constructor;
      . rintro (⟨_, _⟩ | _) <;> tauto;
      . rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp_all;
  rwa [e₁, e₂] at this;

instance : ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, AntiSymmetric, Confluent];

end Kripke


namespace Hilbert.GrzPoint2

open Kripke.Grz

instance Kripke.sound : Sound (Hilbert.GrzPoint2) (Kripke.ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.GrzPoint2) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass

instance complete : Complete (Hilbert.GrzPoint2) (Kripke.ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass) :=
  Kripke.Grz.complete_of_mem_miniCanonicalFrame Kripke.ReflexiveTransitiveAntiSymmetricConfluentFiniteFrameClass $ by
    intro φ;
    refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm, ?_⟩;
    intro X Y Z ⟨⟨RXY₁, RXY₂⟩, ⟨RXZ₁, RXZ₂⟩⟩;
    obtain ⟨U, hU⟩ := ComplementClosedConsistentFinset.lindenbaum (𝓢 := Hilbert.GrzPoint2) (Φ := Y.1 ∪ Z.1) (Ψ := φ.subformulasGrz)
      (by
        apply Finset.union_subset_iff.mpr;
        constructor;
        . intro ψ hψ; exact Y.2.2 |>.subset hψ;
        . intro ψ hψ; exact Z.2.2 |>.subset hψ;
      )
      (by
        simp [FormulaFinset.Consistent];
        sorry;
      );
    use U;
    constructor;
    . constructor;
      . intro ψ _ hψY; exact hU $ Finset.mem_union.mpr (by tauto);
      . intro h;
        ext ξ;
        constructor;
        . intro hξY; exact hU $ Finset.mem_union.mpr (by tauto);
        . sorry;
    . constructor;
      . intro ψ _ hψZ; exact hU $ Finset.mem_union.mpr (by tauto);
      . intro h;
        ext ξ;
        constructor;
        . intro hξZ; exact hU $ Finset.mem_union.mpr (by tauto);
        . sorry;

end Hilbert.GrzPoint2

end LO.Modal
