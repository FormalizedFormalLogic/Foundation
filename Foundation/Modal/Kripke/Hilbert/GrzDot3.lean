import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Dot3

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

abbrev ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel ∧ Connected F.Rel }

instance : ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Dot3 (atom 0) (atom 1)} := by
  have h₁ := restrictFin_definability {Axioms.Dot3 (atom 0) (atom 1)} ({F | Connected F}) $ ConnectedFrameClass.DefinedByDot3
  have := @FiniteFrameClass.definedBy_inter
    ReflexiveTransitiveAntiSymmetricFiniteFrameClass
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)})
    inferInstance
    { F | Connected F.Rel}
    {Axioms.Dot3 (atom 0) (atom 1)}
    h₁;
  have e₁ :
    (ReflexiveTransitiveAntiSymmetricFiniteFrameClass ∩ {F | Connected F.Rel}) =
    (ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass) := by
      ext F;
      simp;
      tauto;
  have e₂ :
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)} ∪ {Axioms.Dot3 (atom 0) (atom 1)}) =
    ({Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0), Axioms.Dot3 (atom 0) (atom 1)} : Set (Formula ℕ)) := by
      ext φ;
      constructor;
      . rintro (⟨_, _⟩ | _) <;> tauto;
      . rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp_all;
  rwa [e₁, e₂] at this;

instance : ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, AntiSymmetric, Connected];

end Kripke


namespace Hilbert.GrzDot3

open Kripke.Grz

instance Kripke.sound : Sound (Hilbert.GrzDot3) (Kripke.ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.GrzDot3) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass

instance complete : Complete (Hilbert.GrzDot3) (Kripke.ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass) :=
  complete_of_mem_miniCanonicalFrame Kripke.ReflexiveTransitiveAntiSymmetricConnectedFiniteFrameClass $ by
    intro φ;
    refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm, ?_⟩;
    intro x y z ⟨⟨Rxy₁, Rxy₂⟩, ⟨Rxz₁, Rxz₂⟩⟩;
    apply or_iff_not_imp_left.mpr;
    intro nRyz;
    rcases (not_and_or.mp nRyz) with (nRyz | nRyz);
    . push_neg at nRyz;
      obtain ⟨ψ, hψ, ⟨hψy, hψz⟩⟩ := nRyz;
      constructor;
      . intro ξ hξ₁ hξ₂;
        apply Rxy₁;
        . exact hξ₁;
        . sorry;
      . intro hyz;
        have exy := Rxy₂ ?_;
        have exz := Rxz₂ ?_;
        tauto;
        . subst exy;
          intro ξ hξ hξz;
          sorry;
        . intro ξ hξ hξy;
          sorry;
    . push_neg at nRyz;
      replace ⟨nRyz₁, nRyz₂⟩ := nRyz;
      constructor;
      . sorry;
      . sorry;

end Hilbert.GrzDot3

end LO.Modal
